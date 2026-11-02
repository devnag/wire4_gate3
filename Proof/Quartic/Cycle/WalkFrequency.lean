import Proof.Quartic.Cycle.FourierCollapse
import Proof.Quartic.Cycle.NoWrap

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler

/-- Paper `lem:cycle`: pull the actual signed Γ_w and mask_w out of the Re/Im walk products. -/
theorem walk_parts_sum {N Q m G₁ G₂ : ℕ} (hm : 0 < m)
    (θ : Frequency m G₁ G₂) (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ)
    (S : Fin Q → Cell N) (w : Walk N m) :
    (∑ ν : Fin 2, ∏ l, (realPartMatrix θ R₁ R₂ mask ν (edge hm w l) *
      gamma S (edge hm w l))) =
      walkGamma hm S w * walkMask hm mask w *
        ((∏ l, (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))).re) +
          ∏ l, (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))).im) := by
  classical
  rw [Fin.sum_univ_two]
  simp only [realPartMatrix_zero, realPartMatrix_one, maskedPhase,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add]
  simp_rw [Finset.prod_mul_distrib]
  unfold walkGamma walkMask
  ring

/-- Paper `lem:cycle`: the actual walk frequency sum, with modular zero converted to INTEGER zero. -/
theorem walk_frequency_parts {N m G₁ G₂ : ℕ} (hm : 0 < m)
    (R₁ R₂ : Cell N → ℤ) (hR₁ : ∀ c, |R₁ c| ≤ G₁) (hR₂ : ∀ c, |R₂ c| ≤ G₂)
    (w : Walk N m) :
    (4 : ℝ)^m * (∑ θ : Frequency m G₁ G₂,
      ((∏ l, (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))).re) +
        ∏ l, (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))).im)) =
      (omega m G₁ : ℝ) * (omega m G₂ : ℝ) *
        ∑ σ : SignPattern m, (kappa m σ : ℝ) *
          (if walkSum hm R₁ σ w = 0 then 1 else 0) *
          (if walkSum hm R₂ σ w = 0 then 1 else 0) := by
  classical
  have h := frequency_parts_sum (G₁ := G₁) (G₂ := G₂)
    (fun l => R₁ (edge hm w l)) (fun l => R₂ (edge hm w l))
  change (4 : ℂ)^m * (∑ θ : Frequency m G₁ G₂,
      ((∏ l, (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))).re : ℂ) +
        ∏ l, (phase θ (R₁ (edge hm w l)) (R₂ (edge hm w l))).im)) =
      (omega m G₁ : ℂ) * (omega m G₂ : ℂ) *
        ∑ σ : SignPattern m, (kappa m σ : ℂ) *
          (if (walkSum hm R₁ σ w : ZMod (omega m G₁)) = 0 then 1 else 0) *
          (if (walkSum hm R₂ σ w : ZMod (omega m G₂)) = 0 then 1 else 0) at h
  simp_rw [walkSum_cast_zero_iff hm R₁ hR₁, walkSum_cast_zero_iff hm R₂ hR₂] at h
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.ofReal_prod, apply_ite, Complex.ofReal_one, Complex.ofReal_zero,
    mul_ite, mul_one, mul_zero] using h

end NearQuarticWires.Cycle
