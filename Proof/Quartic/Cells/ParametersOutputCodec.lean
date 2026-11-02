import Proof.Quartic.Cells.ParametersOutputArithmetic

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- Canonical rational output for a nonnegative quotient uses the
ordinary gcd reduction, Step 5 and `prop:time`, paper/paper.tex. -/
theorem ratWord_nonnegative_quotient (N D : ℕ) (hD : 0 < D) :
    ratWord ((N : ℚ) / D) = natWord 0 ++ natWord (N / Nat.gcd N D) ++ natWord (D / Nat.gcd N D) := by
  have hnum : (mkRat (N : ℤ) D).num = ((N / Nat.gcd N D : ℕ) : ℤ) := by
    simp [Rat.num_mkRat, hD.ne', Nat.gcd_comm]
  have hden : (mkRat (N : ℤ) D).den = D / Nat.gcd N D := by
    simp [Rat.den_mkRat, hD.ne', Nat.gcd_comm]
  have he : (N : ℚ) / D = mkRat (N : ℤ) D := by rw [Rat.mkRat_eq_div]; rfl
  have hsign : ¬ (((N / Nat.gcd N D : ℕ) : ℤ) < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
  rw [he]
  simp only [ratWord, NearCubicGates.Close.Interfaces.intWord, hnum, hden,
    if_neg hsign, Int.natAbs_natCast]

end NearQuarticWires.Cells
