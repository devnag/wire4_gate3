import Proof.Quartic.Cycle.PhaseProduct

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler

/-- Paper `lem:cycle`: a strictly bounded integer has no nonzero modular representative at zero. -/
theorem intCast_eq_zero_iff_of_abs_lt (p : ℕ) (a : ℤ) (ha : |a| < p) :
    (a : ZMod p) = 0 ↔ a = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    have hd : (p : ℤ) ∣ |a| := (dvd_abs _ _).mpr h
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (abs_nonneg a) ha hd
    exact abs_eq_zero.mp hz
  · rintro rfl
    exact dvd_zero _

/-- Paper `lem:cycle`: orthogonality detects equality of the actual signed walk sum. -/
theorem walkSum_cast_zero_iff {N m G : ℕ} (hm : 0 < m)
    (R : Cell N → ℤ) (hR : ∀ c, |R c| ≤ G)
    (σ : SignPattern m) (w : Walk N m) :
    (walkSum hm R σ w : ZMod (omega m G)) = 0 ↔ walkSum hm R σ w = 0 := by
  apply intCast_eq_zero_iff_of_abs_lt
  have hb := abs_walkSum_le hm R G hR σ w
  have hG : (0 : ℤ) ≤ G := by positivity
  push_cast at hb
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  unfold omega
  push_cast
  nlinarith

end NearQuarticWires.Cycle
