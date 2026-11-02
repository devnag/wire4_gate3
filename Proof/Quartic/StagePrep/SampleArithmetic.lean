import Proof.Quartic.Cells.ParametersArithmetic

/-!
# The exact fourth-power sampling comparison

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

/-- The positive integer numerator in the fourth-power sample
test of `sec:params`, paper/paper.tex. -/
def sampleNumerator (N m theta den : ℕ) : ℕ :=
  (1024 * N * m) ^ 4 * (8 * N * N * theta) * den ^ 8

/-- The positive integer denominator in the sample test of
`sec:params`, paper/paper.tex. -/
def sampleDenominator (num : ℕ) : ℕ := num ^ 8

/-- The natural logarithm argument in the sample test of
`sec:params`, paper/paper.tex. -/
def sampleArgument (N m theta num den : ℕ) : ℕ :=
  ⌈((sampleNumerator N m theta den : ℕ) : ℚ) / sampleDenominator num⌉₊

/-- The fourth-power test of `sec:params`, paper/paper.tex, is an exact quotient in the canonical rational
encoding of the sampling precision. -/
theorem sample_ratio_encoding (N m theta num den : ℕ) (eta : ℚ)
    (hnum : eta.num = num) (hden : eta.den = den)
    (hu : 0 < num) (hd : 0 < den) :
    ((((1024 * N * m : ℕ) : ℚ) ^ 4 * ((4 * N ^ 2 * (2 * theta) : ℕ) : ℚ)) / eta ^ 8) =
      ((sampleNumerator N m theta den : ℕ) : ℚ) / sampleDenominator num := by
  have he : eta = (num : ℚ) / den := by
    have h := Rat.num_div_den eta
    rw [hnum, hden] at h
    simpa only [Int.cast_natCast] using h.symm
  have hu0 : (num : ℚ) ≠ 0 := by exact_mod_cast hu.ne'
  have hd0 : (den : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [he]
  unfold sampleNumerator sampleDenominator
  push_cast
  field_simp
  ring

/-- The exact sample exponent in `sec:params`, paper/paper.tex, is the base-sixteen clog of its integer argument. -/
theorem sampleExponent_encoding (N m theta num den : ℕ) (eta : ℚ)
    (hnum : eta.num = num) (hden : eta.den = den)
    (hu : 0 < num) (hd : 0 < den) :
    Cells.ParameterArithmetic.sampleExponent N m (2 * theta) eta =
      Nat.clog 16 (sampleArgument N m theta num den) := by
  unfold Cells.ParameterArithmetic.sampleExponent Cells.ParameterArithmetic.ceilLog
  rw [sample_ratio_encoding N m theta num den eta hnum hden hu hd]
  rfl

end NearQuarticWires.StagePrep
