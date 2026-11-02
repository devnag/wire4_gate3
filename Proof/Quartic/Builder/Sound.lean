import Proof.Quartic.Builder.Exact

/-!
# The counting algorithm on a call and a witness word, and its soundness

Paper: `thm:counter`(i), paper/paper.tex; `sec:params`;
`prop:sound`.

`value c w` is the mathematical counting algorithm of `sec:algorithm` on the call `c` and the witness word `w`:
* a call outside the normalized shape, `n < 4`, or a failed parameter requirement gives the sound default
  `(1/2, 1/2)`;
* `W = 0`: the circuits are constant and the call is evaluated exactly (`closedValue`, equal to `(p_true, 0)` by
  `closedValue_eq`);
* otherwise the parameters are those of the exact rules `Cells.prepare` (the one parameter supplier, with all rules
  in `Cells.ParameterRules`), and the value is `Algorithm.CellCall.run` on the cell call built from `c` and `w`.

The branches are those of `Cells.preparedPlan` (`value_eq_run`). Soundness holds for every call and every witness
(`value_sound`): the run branch is `Algorithm.CellCall.prop_sound_of_parameters`, whose hypotheses are supplied by
`Builder.usesParameters`, `Builder.partitionAverage`, `Builder.fourierRows`, `Builder.residual_le`,
`Builder.residual_zero`, `Builder.two_le_N` and `Builder.N_le_Q`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces

/-- **The counting algorithm** of `sec:algorithm` on a call and a witness word (paper/paper.tex),
following the outcomes of `Cells.preparedPlan`. -/
noncomputable def value (c : Call) (w : List Bool) : ℚ × ℚ := by
  classical
  exact if Shaped c then
      if c.n < 4 then Algorithm.soundDefault
      else if Transfer.callWires c = 0 then closedValue c
      else match h : Cells.prepare (callInput c) with
        | none => Algorithm.soundDefault
        | some p => (cellCall c (Cells.prepare_spec _ p h) w).run
    else Algorithm.soundDefault

/-- The acceptance probability lies in `[0, 1]`. -/
theorem prob_mem (c : Call) : 0 ≤ c.prob ∧ c.prob ≤ 1 := by
  unfold Call.prob
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  have h := Finset.card_filter_le (Finset.univ : Finset (BitInput c.n)) (fun z => c.predicate z = true)
  rw [Finset.card_univ] at h
  have hcard : Fintype.card (BitInput c.n) = 2 ^ c.n := by simp [BitInput]
  rw [hcard] at h
  exact_mod_cast h

/-- `sec:params`, paper/paper.tex: the sound default `(1/2, 1/2)` contains every probability. -/
theorem soundDefault_sound (c : Call) :
    |Algorithm.soundDefault.1 - c.prob| ≤ Algorithm.soundDefault.2 := by
  obtain ⟨h0, h1⟩ := prob_mem c
  simp only [Algorithm.soundDefault]
  rw [abs_le]
  constructor <;> linarith

/-- **`prop:sound` for a call** (paper/paper.tex): on a shaped call whose parameters are selected,
the algorithm run on the cell call of any witness word returns `(p̂, κ̂)` with `|p̂ - p_true| ≤ κ̂`. -/
theorem cellCall_sound (c : Call) (hc : Shaped c) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (callInput c) p) (w : List Bool) :
    |(cellCall c hs w).run.1 - c.prob| ≤ (cellCall c hs w).run.2 :=
  (cellCall c hs w).prop_sound_of_parameters (algorithmParameters c hs) (usesParameters c hs w) c.prob
    (partitionAverage c hs w) (fourierRows c hs w hc) (residual_le c hs w) (residual_zero c hs w hc)
    (two_le_N c hs w) (N_le_Q c hs w)

/-- **Soundness for every witness** (`thm:counter`(i), paper/paper.tex): for every call and every
witness word, `|p̂ - Pr_x[pred(x) = 1]| ≤ κ̂`. -/
theorem value_sound (c : Call) (w : List Bool) : |(value c w).1 - c.prob| ≤ (value c w).2 := by
  classical
  unfold value
  split_ifs with hc hn hW
  · exact soundDefault_sound c
  · rw [closedValue_eq c hc hW]
    simp
  · split
    · exact soundDefault_sound c
    · exact cellCall_sound c hc _ w
  · exact soundDefault_sound c

/-- The branches of `value` are those of the plan `Cells.preparedPlan`: when the exact rules select parameters, the
value is the algorithm run on the cell call. -/
theorem value_eq_run (c : Call) (hc : Shaped c) (hW : Transfer.callWires c ≠ 0) {p : Cells.Parameters}
    (h : Cells.prepare (callInput c) = some p) (w : List Bool) :
    value c w = (cellCall c (Cells.prepare_spec _ p h) w).run := by
  classical
  have hn : ¬ c.n < 4 := by
    have := (Cells.prepare_spec _ p h).input_valid.1
    change 4 ≤ c.n at this
    omega
  unfold value
  rw [if_pos hc, if_neg hn, if_neg hW]
  split
  next h' =>
    rw [h] at h'
    cases h'
  next p' h' =>
    have hp : p = p' := by
      rw [h] at h'
      exact Option.some.inj h'
    subst hp
    rfl

/-- The plan followed by `value` is `Cells.preparedPlan`: for a shaped call with `W > 0` and selected parameters,
the plan runs Steps 1–5 with the parameters `Cells.toAlgorithmParameters` used by the cell call
(`Builder.usesParameters`). -/
theorem preparedPlan_eq (c : Call) {p : Cells.Parameters} (h : Cells.prepare (callInput c) = some p) :
    Cells.preparedPlan (callInput c) =
      .run (algorithmParameters c (Cells.prepare_spec _ p h)) :=
  Cells.preparedPlan_run _ p h

end NearQuarticWires.Builder
