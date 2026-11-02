import Proof.Quartic.StagePrep.PrefixBudget
import Proof.Quartic.StagePrep.WordCases

/-!
# The original preparation request has a public read prefix

Paper: the witness in `sec:algorithm`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Interfaces

/-- The number of witness bits requested by preparation in
`sec:algorithm`, paper/paper.tex. Every closed
or rejected dispatch reads zero witness bits. -/
noncomputable def preparationReadLength (B1 B2 : ℕ) (c : Call) : ℕ :=
  match Program.dispatch B1 B2 c with
  | none => 0
  | some p => Program.witnessReadLength c p.1

/-- The witness read in `prop:time`, paper/paper.tex, is bounded by a fixed polynomial in the original
arity on every call, including malformed calls and long witnesses. -/
theorem preparationReadLength_bound (B1 B2 : ℕ) (c : Call) :
    preparationReadLength B1 B2 c ≤ 5*(c.n+1)^5 := by
  unfold preparationReadLength
  cases hd : Program.dispatch B1 B2 c with
  | none => exact Nat.zero_le _
  | some p => exact witnessReadLength_preparation_bound c p.1 (Cells.prepare_spec _ _ p.2)

/-- The preparation word of `prop:time`, paper/paper.tex, is unchanged when two witnesses agree on the
publicly bounded prefix. No witness suffix enters its output. -/
theorem prepWord_congr_public_prefix (B1 B2 : ℕ) (c : Call) (w w' : List Bool)
    (h : ∀ i<preparationReadLength B1 B2 c,
      Algorithm.witnessBit w i=Algorithm.witnessBit w' i) :
    Program.prepWord B1 B2 c w=Program.prepWord B1 B2 c w' := by
  classical
  cases hd : Program.dispatch B1 B2 c with
  | none =>
    by_cases ha : Transfer.Admitted4 B1 B2 c
    · by_cases hz : Transfer.callWires c=0
      · rw [prepWord_of_zero c w ha hz,prepWord_of_zero c w' ha hz]
      · have hp : Cells.prepare (Builder.callInput c)=none := by
          cases hp : Cells.prepare (Builder.callInput c) with
          | none => rfl
          | some p =>
            unfold Program.dispatch at hd
            rw [if_pos ⟨ha,hz⟩] at hd
            split at hd
            · contradiction
            · rename_i hnone
              rw [hp] at hnone
              contradiction
        rw [prepWord_of_prepare_none c w ha hz hp,prepWord_of_prepare_none c w' ha hz hp]
    · rw [prepWord_of_not_admitted c w ha,prepWord_of_not_admitted c w' ha]
  | some p =>
    have hp : Program.witnessPrefix c p.1 w=Program.witnessPrefix c p.1 w' := by
      apply List.ext_getElem (by simp [Program.witnessPrefix])
      intro i hi hi'
      simp only [Program.witnessPrefix,List.getElem_ofFn]
      apply h
      simpa only [Program.witnessPrefix,List.length_ofFn,preparationReadLength,hd] using hi
    rw [prepWord_of_dispatch c w p hd,prepWord_of_dispatch c w' p hd,hp]

end NearQuarticWires.StagePrep
