import Proof.Quartic.Cycle.Identity
import Proof.Quartic.Cycle.ConditionalGamma

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler
open NearCubicWires.WireExponent3_5.Sampler (completion)

/-- Paper `cor:conditional`: the actual finite conditional mean
of the concrete dilation potential, with the low prefix bits fixed. -/
noncomputable def conditionalPotential {G₁ G₂ : ℕ} (P : SeedParameters)
    (R₁ R₂ : Cell P.N → ℤ) (mask : Cell P.N → ℝ) (plen pre : ℕ) : ℝ :=
  (∑ r ∈ Finset.range (2^(seedLength P-plen)),
    columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask
      (seedSample P (completion plen pre r))) / (2 : ℝ)^(seedLength P-plen)

/-- Paper `cor:conditional`: the rational coefficient is exactly
the conditional mean of the SIGNED real walk product. -/
theorem conditionalGamma_real (P : SeedParameters) (plen pre : ℕ) (w : Walk P.N 4) :
    (conditionalGamma P plen pre w : ℝ) =
      (∑ r ∈ Finset.range (2^(seedLength P-plen)),
        walkGamma (by norm_num) (seedSample P (completion plen pre r)) w) /
        (2 : ℝ)^(seedLength P-plen) := by
  simp [conditionalGamma, gammaCompletionSum, walkGammaInt_cast]

/-- Paper `cor:conditional`: the FULL concrete conditional cycle identity.
Every column dependence remains in the mask and the two INTEGER walk equations;
the dyadic signed coefficient depends only on prefix and walk. -/
theorem conditional_cycle_sum_identity {G₁ G₂ : ℕ} (P : SeedParameters)
    (R₁ R₂ : Cell P.N → ℤ) (mask : Cell P.N → ℝ)
    (hR₁ : ∀ c, |R₁ c| ≤ G₁) (hR₂ : ∀ c, |R₂ c| ≤ G₂) (plen pre : ℕ) :
    conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask plen pre =
      (2 * (Fintype.card (Frequency 4 G₁ G₂) : ℝ) / (4 : ℝ)^4) *
        ∑ w : Walk P.N 4, (conditionalGamma P plen pre w : ℝ) *
          walkMask (by norm_num) mask w *
          ∑ σ : SignPattern 4, (kappa 4 σ : ℝ) *
            (if walkSum (by norm_num) R₁ σ w = 0 then 1 else 0) *
            (if walkSum (by norm_num) R₂ σ w = 0 then 1 else 0) := by
  classical
  unfold conditionalPotential
  simp_rw [cycle_sum_identity R₁ R₂ mask _ hR₁ hR₂]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [conditionalGamma_real, div_mul_eq_mul_div]
  simp_rw [← Finset.sum_mul]
  rw [← Finset.sum_div]
  ring

#print axioms conditional_cycle_sum_identity
end NearQuarticWires.Cycle
