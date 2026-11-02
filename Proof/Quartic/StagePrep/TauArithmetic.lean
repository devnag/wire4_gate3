import Proof.Quartic.Cells.ParametersArithmetic
import Proof.Gates.Dispatch.ParamsMath

/-!
# Integer arithmetic for the masking threshold

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The reciprocal in `sec:params`, paper/paper.tex, uses the original exact rational encoding. -/
theorem sixteen_div_beta (beta : ℚ) (num den : ℕ)
    (hnum : beta.num = num) (hden : beta.den = den) :
    16 / beta = ((16 * den : ℕ) : ℚ) / num := by
  have hb : beta = (num : ℚ) / den := by
    have h := Rat.num_div_den beta
    rw [hnum, hden] at h
    simpa only [Int.cast_natCast] using h.symm
  rw [hb]
  push_cast
  rw [div_div_eq_mul_div]

/-- The masking logarithm of `sec:params`, paper/paper.tex, is a natural ceiling followed by a binary clog. -/
theorem tau_log_encoding (beta : ℚ) (num den : ℕ)
    (hnum : beta.num = num) (hden : beta.den = den) :
    Cells.ParameterArithmetic.ceilLog 2 (16 / beta) =
      Nat.clog 2 ⌈((16 * den : ℕ) : ℚ) / num⌉₊ := by
  rw [Cells.ParameterArithmetic.ceilLog, sixteen_div_beta beta num den hnum hden]

/-- The intermediate rational ceiling of `sec:params`,
paper/paper.tex, is bounded without any later
parameter-success assumption. -/
theorem tau_ceil_bound (num den : ℕ) (hnum : 0 < num) :
    ⌈((16 * den : ℕ) : ℚ) / num⌉₊ ≤ 16 * den + num := by
  rw [ceil_div_nat _ _ hnum]
  exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

end NearQuarticWires.StagePrep
