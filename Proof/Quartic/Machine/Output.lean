import Proof.Quartic.Machine.StepSemantics

set_option autoImplicit false

namespace NearQuarticWires.Machine

/-- `sec:algorithm`, paper/paper.tex: multiplying the rounded
center by `2^(n+1)` gives an explicit integer, even for signed endpoints. -/
theorem roundedInterval_center_scaled (n : ℕ) (lo hi : ℚ) :
    (roundedInterval n lo hi).1 * 2 ^ (n + 1) =
      ((⌊lo * 2 ^ n⌋ + ⌈hi * 2 ^ n⌉ : ℤ) : ℚ) := by
  dsimp [roundedInterval, dyadicFloor, dyadicCeil]
  rw [pow_succ]
  push_cast
  field_simp

/-- `sec:algorithm`, paper/paper.tex: multiplying the rounded
radius by `2^(n+1)` gives an explicit integer. -/
theorem roundedInterval_radius_scaled (n : ℕ) (lo hi : ℚ) :
    (roundedInterval n lo hi).2 * 2 ^ (n + 1) =
      ((⌈hi * 2 ^ n⌉ - ⌊lo * 2 ^ n⌋ : ℤ) : ℚ) := by
  dsimp [roundedInterval, dyadicFloor, dyadicCeil]
  rw [pow_succ]
  push_cast
  field_simp

/-- `thm:counter`, paper/paper.tex, and `prop:time`:
the actual rounded center and radius meet the `Counter4.den` shape. -/
theorem roundedInterval_den (n : ℕ) (lo hi : ℚ) :
    ((roundedInterval n lo hi).1 * 2 ^ (n + 1)).den = 1 ∧
      ((roundedInterval n lo hi).2 * 2 ^ (n + 1)).den = 1 := by
  rw [roundedInterval_center_scaled, roundedInterval_radius_scaled]
  simp

/-- `thm:counter`, paper/paper.tex: both values are dyadic in the
literal existing interface, with the SAME denominator exponent `n+1`. -/
theorem roundedInterval_dyadic (n : ℕ) (lo hi : ℚ) :
    NearCubicGates.Close.Interfaces.IsDyadic (roundedInterval n lo hi).1 ∧
      NearCubicGates.Close.Interfaces.IsDyadic (roundedInterval n lo hi).2 := by
  obtain ⟨hc, hr⟩ := roundedInterval_den n lo hi
  exact ⟨⟨n + 1, hc⟩, ⟨n + 1, hr⟩⟩

end NearQuarticWires.Machine
