import Proof.Quartic.Cells.ParametersOutputBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells

/-- Outward rounding preserves the nonnegative upper endpoint,
center and radius in Step 5, `prop:sound`, paper/paper.tex. -/
theorem rounded_output_numerators_nonneg (n : ℕ) (lo hi : ℚ)
    (hhi : 0 ≤ hi) (horder : lo ≤ hi) (hcenter : 0 ≤ lo + hi) :
    0 ≤ ⌈hi * 2 ^ n⌉ ∧
      0 ≤ ⌊lo * 2 ^ n⌋ + ⌈hi * 2 ^ n⌉ ∧
      0 ≤ ⌈hi * 2 ^ n⌉ - ⌊lo * 2 ^ n⌋ := by
  have hp : (0 : ℚ) ≤ 2 ^ n := by positivity
  have hG : (0 : ℤ) ≤ ⌈hi * 2 ^ n⌉ := by
    exact Int.ceil_nonneg (mul_nonneg hhi hp)
  have hFG : ⌊lo * 2 ^ n⌋ ≤ ⌈hi * 2 ^ n⌉ := by
    have hcast : ((⌊lo * 2 ^ n⌋ : ℤ) : ℚ) ≤ ((⌈hi * 2 ^ n⌉ : ℤ) : ℚ) :=
      (Int.floor_le _).trans ((mul_le_mul_of_nonneg_right horder hp).trans (Int.le_ceil _))
    exact_mod_cast hcast
  have hneg : -(hi * 2 ^ n) ≤ lo * 2 ^ n := by
    have : -hi ≤ lo := by linarith
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right this hp
  have hsum : -⌈hi * 2 ^ n⌉ ≤ ⌊lo * 2 ^ n⌋ := by
    rw [← Int.floor_neg]
    exact Int.floor_mono hneg
  exact ⟨hG, by omega, by omega⟩

end NearQuarticWires.Cells
