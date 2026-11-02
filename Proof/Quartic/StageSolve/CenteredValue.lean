import Proof.Quartic.StageSolve.ResidueRequest
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false

namespace NearQuarticWires.StageSolve

open NearCubicGates.Close.WordPrograms.SInt

/-- `lem:residue`, paper/paper.tex: centered decoding from
an unsigned remainder and the original sign. The two cutoffs retain
the positive endpoint when the modulus is even. -/
def centeredMagnitude (q magnitude : ℕ) (negative : Bool) : ℤ :=
  if q = 0 then sval magnitude negative else
    let rem := magnitude % q
    if (q - negative.toNat) / 2 < rem then sval (q - rem) (!negative)
      else sval rem negative

/-- `lem:residue`, paper/paper.tex: this branch description gives
the specified half-open centered interval for both input signs. -/
theorem centeredMagnitude_eq (q magnitude : ℕ) (negative : Bool) :
    centeredMagnitude q magnitude negative =
      Walks.centeredResidue (q : ℤ) (sval magnitude negative) := by
  by_cases hq : q = 0
  · subst q
    simp [centeredMagnitude, Walks.centeredResidue]
  have hq0 : 0 < q := by omega
  have hr := Nat.mod_lt magnitude hq0
  have hmod : (magnitude : ℤ) ≡ (magnitude % q : ℕ) [ZMOD (q : ℤ)] := by
    exact (Int.mod_modEq (magnitude : ℤ) (q : ℤ)).symm
  have hqmod : (q : ℤ) ≡ 0 [ZMOD (q : ℤ)] := by simp [Int.ModEq]
  cases negative with
  | false =>
    simp only [centeredMagnitude, hq, if_false, Bool.toNat_false, Nat.sub_zero,
      Bool.not_false, sval, Bool.false_eq_true, if_true]
    by_cases hc : q / 2 < magnitude % q
    · simp only [hc, if_true]
      apply Eq.symm
      apply Walks.centeredResidue_eq _ _ _ (by omega)
      · simpa [Int.natCast_sub (Nat.le_of_lt hr)] using hmod.sub hqmod.symm
      · rw [Int.natCast_sub (Nat.le_of_lt hr)]; omega
      · rw [Int.natCast_sub (Nat.le_of_lt hr)]; omega
    · simp only [hc, if_false]
      exact (Walks.centeredResidue_eq _ _ _ (by omega) hmod (by omega) (by omega)).symm
  | true =>
    simp only [centeredMagnitude, hq, if_false, Bool.toNat_true, Bool.not_true,
      sval, Bool.false_eq_true, if_true]
    by_cases hc : (q - 1) / 2 < magnitude % q
    · simp only [hc, if_true]
      apply Eq.symm
      apply Walks.centeredResidue_eq _ _ _ (by omega)
      · have h := hmod.neg.add hqmod.symm
        rw [Int.natCast_sub (Nat.le_of_lt hr)]
        convert h using 1 <;> ring
      · rw [Int.natCast_sub (Nat.le_of_lt hr)]; omega
      · rw [Int.natCast_sub (Nat.le_of_lt hr)]; omega
    · simp only [hc, if_false]
      exact (Walks.centeredResidue_eq _ _ _ (by omega) hmod.neg (by omega) (by omega)).symm

/-- `lem:residue`, paper/paper.tex: the centered arithmetic
algorithm agrees with the exact child-subroutine target. -/
theorem residueValue_eq_centeredMagnitude (r : ResidueRequest) :
    residueValue r = centeredMagnitude r.modulus r.value.natAbs (decide (r.value < 0)) := by
  rw [centeredMagnitude_eq, sval_natAbs]
  rfl

end NearQuarticWires.StageSolve
