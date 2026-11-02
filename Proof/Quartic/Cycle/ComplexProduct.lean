import Proof.Quartic.Cycle.SignProduct

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset Complex

/-- Paper `lem:cycle`: the actual Re/Im product expansion,
without choosing a real argument of the Fourier characters. -/
theorem re_im_product (m : ℕ) (z : Fin (2 * m) → ℂ) :
    (4 : ℂ)^m * ((∏ i, (z i).re : ℂ) + ∏ i, (z i).im) =
      ∑ σ : Fin (2*m) → Bool,
        (1 + (-1 : ℂ)^m * ∏ i, choiceSign (R := ℂ) (σ i)) *
          ∏ i, if σ i then z i else star (z i) := by
  classical
  have hplus (i : Fin (2*m)) : z i + star (z i) = 2 * ((z i).re : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hminus (i : Fin (2*m)) : z i - star (z i) =
      (2 * I) * ((z i).im : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hcancel : (-1 : ℂ)^m * I^(2*m) = 1 := by
    rw [pow_mul, Complex.I_sq, ← mul_pow]
    norm_num
  have hpow : (-1 : ℂ)^m * ((4 : ℂ)^m * I^(2*m)) = (4 : ℂ)^m := by
    calc
      _ = (4 : ℂ)^m * ((-1 : ℂ)^m * I^(2*m)) := by ring
      _ = _ := by rw [hcancel, mul_one]
  have htwo : (2 : ℂ)^(2*m) = (4 : ℂ)^m := by
    rw [pow_mul]
    norm_num
  have h := cycle_sign_product z (fun i => star (z i)) m
  simp_rw [hplus, hminus] at h
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at h
  rw [htwo, ← mul_assoc, hpow] at h
  simpa only [mul_add, ← Complex.ofReal_prod] using h

#print axioms re_im_product
end NearQuarticWires.Cycle
