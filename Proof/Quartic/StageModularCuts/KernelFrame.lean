import Proof.Quartic.StageModularCuts.Kernel

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: coefficient
reduction returns every stream head to its original position. -/
theorem coefficientFinal_heads (a : State) (p : ℕ) (z : ℤ) (q : ℕ) :
    (coefficientFinal a p z q).sh = a.sh := by
  by_cases hz : z < 0 <;>
    simp [coefficientFinal, corrected, negativeState, divided, splitState, hz]

/-- `lem:print`, paper/paper.tex: the signed result
has exactly the original field width and a nonnegative residue. -/
theorem coefficientFinal_word (a : State) (p : ℕ) (z : ℤ) (q : ℕ) :
    (coefficientFinal a p z q).st coefficient =
      frame (MatrixScoreBatch.signMagnitude p (z % (q : ℤ))) := by
  simp only [coefficientFinal, WState.setv_st, WState.sets_st, Function.update_self,
    SInt.signMagnitude_eq]

/-- `lem:print`, paper/paper.tex: coefficient
reduction restores every scalar register, including the sign flag. -/
theorem coefficientFinal_registers (a : State) (p : ℕ) (z : ℤ) (q : ℕ)
    (hs : a.val sign = 0) : (coefficientFinal a p z q).val = a.val := by
  funext j
  by_cases hj : j = sign
  · subst hj
    simp [coefficientFinal, hs]
  · by_cases hz : z < 0 <;>
      simp [coefficientFinal, corrected, negativeState, divided, splitState, hz, hj]

/-- `lem:print`, paper/paper.tex: only the coefficient
and its four binary scratch words are changed; all affine bytes and
source/output cursors are preserved. -/
theorem coefficientFinal_frame (a : State) (p : ℕ) (z : ℤ) (q : ℕ)
    (hs : a.val sign = 0) :
    SameExcept a (coefficientFinal a p z q)
      [coefficient, magnitude, quotient, remainder, temporary] [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have hne : j ≠ coefficient ∧ j ≠ magnitude ∧ j ≠ quotient ∧ j ≠ remainder ∧ j ≠ temporary := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hj
    constructor
    · by_cases hz : z < 0 <;>
        simp [coefficientFinal, corrected, negativeState, divided, splitState, hz,
          hne.1, hne.2.1, hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2]
    · rw [coefficientFinal_heads]
  · intro j _
    rw [coefficientFinal_registers a p z q hs]
  · by_cases hz : z < 0 <;>
      simp [coefficientFinal, corrected, negativeState, divided, splitState, hz]

/-- `lem:print`, paper/paper.tex: the binary
workspace after one coefficient is valid for the next coefficient. -/
theorem coefficientFinal_words (a : State) (p : ℕ) (z : ℤ) (q x u v t : ℕ)
    (hw : Words a (p + 1) x q u v t) :
    ∃ x' u', Words (coefficientFinal a p z q) (p + 1) x' q u'
      (StageRecovery.signedNaturalResidue q z.natAbs (decide (z < 0))) 0 := by
  have h1 := divided_words (splitState a p z) (p + 1) z.natAbs q u v t
    (splitState_words a p q x u v t z hw)
  have h2 := corrected_words _ (p + 1) z.natAbs q (z.natAbs / q) (z.natAbs % q)
    (decide (z < 0)) h1
  refine ⟨(if decide (z < 0) then q - z.natAbs % q else z.natAbs),
    (if decide (z < 0) then (q - z.natAbs % q) / q else z.natAbs / q), ?_⟩
  constructor
  · exact BinW.numOn_setv (BinW.numOn_sets_ne h2.input (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne h2.divisor (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne h2.quotient (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne h2.remainder (by decide) _) _ _
  · exact BinW.numOn_setv (BinW.numOn_sets_ne h2.temporary (by decide) _) _ _

end NearQuarticWires.StageModularCuts
