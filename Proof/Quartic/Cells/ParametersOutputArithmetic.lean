import Proof.Quartic.Cells.ParametersOutputBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells

/-- The positive integer denominator for the two scaled endpoints
in Step 5, `sec:algorithm`, paper/paper.tex. -/
def outputDenominator (p : Parameters) : ℕ := p.Q * p.eta.den

/-- The positive part of the scaled lower numerator in Step 5,
`sec:algorithm`, paper/paper.tex. -/
def outputLowerPositive (p : Parameters) (A : ℤ) : ℕ :=
  2 ^ p.k * A.natAbs * p.eta.den

/-- The negative part of the scaled lower numerator in Step 5,
`sec:algorithm`, paper/paper.tex. -/
def outputLowerNegative (p : Parameters) (nc : ℕ) : ℕ :=
  2 ^ p.k * 2 * p.MF * nc * p.eta.num.natAbs * p.Q

/-- The positive part of the scaled upper numerator in Step 5,
`sec:algorithm`, paper/paper.tex. -/
def outputUpperPositive (n : ℕ) (p : Parameters) (A : ℤ) (nc : ℕ) : ℕ :=
  2 ^ p.k * (A.natAbs * p.eta.den + (2 * p.MF + 1) * nc * p.eta.num.natAbs * p.Q) +
    2 ^ n * outputDenominator p

/-- The negative part of the scaled upper numerator in Step 5,
`sec:algorithm`, paper/paper.tex. -/
def outputUpperNegative (p : Parameters) (M : ℤ) : ℕ :=
  2 ^ p.k * M.natAbs * p.eta.den

/-- The denominator of the exact integer arithmetic of Step 5 is
positive, `sec:algorithm`, paper/paper.tex. -/
theorem outputDenominator_pos (p : Parameters) (hQ : 0 < p.Q) :
    0 < outputDenominator p := Nat.mul_pos hQ p.eta.pos

/-- The scaled lower endpoint is an explicit difference of natural
numerators over a positive denominator, Step 5, `sec:algorithm`, paper/paper.tex. This identity uses the actual sign-magnitude codec. -/
theorem stepFiveLower_integer_fraction (n : ℕ) (p : Parameters) (A : ℤ) (nc : ℕ)
    (hk : p.k ≤ n) (hQ : 0 < p.Q) (hη : 0 ≤ p.eta) (hA : 0 ≤ A) :
    Program.stepFiveLower n p A nc * 2 ^ n =
      (((outputLowerPositive p A : ℤ) - (outputLowerNegative p nc : ℤ) : ℤ) : ℚ) /
        outputDenominator p := by
  have ha : (0 : ℚ) ≤ (A : ℚ) := by exact_mod_cast hA
  have he : (p.eta.num.natAbs : ℚ) = (p.eta.num : ℚ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hη)]
  have hn : (0 : ℚ) ≤ (p.eta.num : ℚ) := by exact_mod_cast Rat.num_nonneg.mpr hη
  have heta : p.eta = (p.eta.num.natAbs : ℚ) / p.eta.den := by rw [he, p.eta.num_div_den]
  have hp : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - p.k) * 2 ^ p.k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hq : (p.Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hd : (p.eta.den : ℚ) ≠ 0 := by exact_mod_cast p.eta.den_ne_zero
  have hpow : (2 : ℚ) ^ (n - p.k) ≠ 0 := by positivity
  unfold Program.stepFiveLower outputLowerPositive outputLowerNegative outputDenominator
  conv_lhs => rw [heta, hp]
  push_cast
  rw [abs_of_nonneg ha, abs_of_nonneg hn]
  field_simp [hq, hd, hpow]
  rw [he]

/-- The scaled upper endpoint is an explicit difference of natural
numerators over the same positive denominator, Step 5,
`sec:algorithm`, paper/paper.tex. -/
theorem stepFiveUpper_integer_fraction (n : ℕ) (p : Parameters) (A M : ℤ) (nc : ℕ)
    (hk : p.k ≤ n) (hQ : 0 < p.Q) (hη : 0 ≤ p.eta) (hA : 0 ≤ A) (hM : 0 ≤ M) :
    Program.stepFiveUpper n p A M nc * 2 ^ n =
      (((outputUpperPositive n p A nc : ℤ) - (outputUpperNegative p M : ℤ) : ℤ) : ℚ) /
        outputDenominator p := by
  have ha : (0 : ℚ) ≤ (A : ℚ) := by exact_mod_cast hA
  have hm : (0 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM
  have he : (p.eta.num.natAbs : ℚ) = (p.eta.num : ℚ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hη)]
  have hn : (0 : ℚ) ≤ (p.eta.num : ℚ) := by exact_mod_cast Rat.num_nonneg.mpr hη
  have heta : p.eta = (p.eta.num.natAbs : ℚ) / p.eta.den := by rw [he, p.eta.num_div_den]
  have hp : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - p.k) * 2 ^ p.k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hq : (p.Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hd : (p.eta.den : ℚ) ≠ 0 := by exact_mod_cast p.eta.den_ne_zero
  have hpow : (2 : ℚ) ^ (n - p.k) ≠ 0 := by positivity
  unfold Program.stepFiveUpper outputUpperPositive outputUpperNegative outputDenominator
  conv_lhs => rw [heta]
  push_cast
  rw [abs_of_nonneg ha, abs_of_nonneg hm, abs_of_nonneg hn, hp]
  field_simp [hq, hd, hpow]
  rw [he]
  ring

end NearQuarticWires.Cells
