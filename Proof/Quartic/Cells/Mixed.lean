import Proof.Quartic.Cells.Score

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires Finset
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:mixed`, paper/paper.tex: the four-corner residual written with literal flip sets. -/
theorem delta_eq_flipSets (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) :
    delta P g c u v = mixedDiffSet g.eval (P.flipSet P.leftBlock u) (P.flipSet P.rightBlock v) c := by
  unfold delta mixedDifference mixedDiffSet
  simp only [P.xorInput_errorVector, xorSet_comm]

/-- `lem:mixed`, paper/paper.tex: missing the right flip set forces zero residual. -/
theorem delta_eq_zero_of_right_miss (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors)
    (hmiss : ∀ i ∈ P.flipSet P.rightBlock v, g.weight i = 0) : delta P g c u v = 0 := by
  rw [delta_eq_flipSets]
  exact mixed_eq_zero_of_miss _ _ _ (eval_xorSet_of_disjoint g _ hmiss) c

/-- `lem:mixed`, paper/paper.tex: missing the left flip set forces zero residual. -/
theorem delta_eq_zero_of_left_miss (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors)
    (hmiss : ∀ i ∈ P.flipSet P.leftBlock u, g.weight i = 0) : delta P g c u v = 0 := by
  rw [delta_eq_flipSets]
  unfold mixedDiffSet
  rw [eval_xorSet_of_disjoint g _ hmiss, eval_xorSet_of_disjoint g _ hmiss]
  ring

/-- `lem:mixed`, paper/paper.tex: every nonzero residual reads a flipped coordinate on each side. -/
theorem delta_nonzero_support (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) (h : delta P g c u v ≠ 0) :
    (∃ i ∈ P.flipSet P.leftBlock u, g.weight i ≠ 0) ∧
      (∃ i ∈ P.flipSet P.rightBlock v, g.weight i ≠ 0) := by
  constructor
  · by_contra hm
    push Not at hm
    exact h (delta_eq_zero_of_left_miss P g c u v hm)
  · by_contra hm
    push Not at hm
    exact h (delta_eq_zero_of_right_miss P g c u v hm)

/-- `lem:mixed`, paper/paper.tex: one occurrence's population is charged to an incident flip. -/
theorem delta_natAbs_le_incident (P : StarParams) (g : NormalizedThresholdGate P.n)
    (c : BitInput P.n) (u v : P.Errors) (F : Finset (Fin P.n))
    (hF : delta P g c u v ≠ 0 → ∃ i ∈ F, g.weight i ≠ 0) :
    (delta P g c u v).natAbs ≤ ∑ i ∈ F, if g.weight i ≠ 0 then 1 else 0 := by
  rw [delta_natAbs_eq_indicator]
  split_ifs with h
  · obtain ⟨i, hi, hw⟩ := hF h
    have hh := Finset.single_le_sum (f := fun i => if g.weight i ≠ 0 then (1 : ℕ) else 0)
      (fun i _ => Nat.zero_le _) hi
    simpa [hw] using hh
  · exact Nat.zero_le _

/-- `lem:mixed`, paper/paper.tex: the actual population is bounded by both incidence sums. -/
theorem population_le_incidence (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) :
    population P gates c u v ≤ min (∑ i ∈ P.flipSet P.leftBlock u, incidence gates i)
      (∑ i ∈ P.flipSet P.rightBlock v, incidence gates i) := by
  apply le_min
  · induction gates with
    | nil => simp [population, incidence]
    | cons g gates ih =>
      have hg := delta_natAbs_le_incident P g c u v (P.flipSet P.leftBlock u)
        (fun h => (delta_nonzero_support P g c u v h).1)
      simp only [population, incidence, List.map_cons, List.sum_cons, Finset.sum_add_distrib] at ih ⊢
      exact Nat.add_le_add hg ih
  · induction gates with
    | nil => simp [population, incidence]
    | cons g gates ih =>
      have hg := delta_natAbs_le_incident P g c u v (P.flipSet P.rightBlock v)
        (fun h => (delta_nonzero_support P g c u v h).2)
      simp only [population, incidence, List.map_cons, List.sum_cons, Finset.sum_add_distrib] at ih ⊢
      exact Nat.add_le_add hg ih

end NearQuarticWires.Cells
