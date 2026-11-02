import Proof.Quartic.Cycle.ConditionalIdentity

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler
open NearCubicWires.WireExponent3_5.Sampler (completion)

/-- `cor:conditional`, paper/paper.tex: the signed integer
coefficient has the stated dyadic numerator bound. -/
theorem abs_scaledGamma_le (P : SeedParameters) (plen pre : ℕ)
    (hplen : plen ≤ seedLength P) (w : Walk P.N 4) :
    |scaledGamma P plen pre w| ≤
      (2 : ℤ)^(seedLength P) * ((P.Q : ℤ)*(P.N : ℤ)^2)^8 := by
  have h := abs_conditionalGamma_le P plen pre w
  have he := scaledGamma_spec P plen pre hplen w
  have hr : |(scaledGamma P plen pre w : ℚ)| ≤
      (2 : ℚ)^(seedLength P) * ((P.Q : ℚ)*(P.N : ℚ)^2)^8 := by
    rw [← he, abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 2^(seedLength P))]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  exact_mod_cast hr

/-- `lem:cycle`, paper/paper.tex: the concrete cycle potential
is nonnegative, although its walk expansion has signed coefficients. -/
theorem columnPotential_nonneg {N Q G₁ G₂ : ℕ}
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (S : Fin Q → Cell N) :
    0 ≤ columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S := by
  unfold columnPotential
  apply Finset.sum_nonneg
  intro θ _
  apply Finset.sum_nonneg
  intro ν _
  rw [trace_dilation_eight]
  exact mul_nonneg (by norm_num)
    (NearCubicWires.WireExponent3_5.Sampler.trace_pow4_nonneg _)

/-- `cor:conditional`, paper/paper.tex: every prefix has a
nonnegative conditional potential, with no sign assumption on its walk weights. -/
theorem conditionalPotential_nonneg {G₁ G₂ : ℕ} (P : SeedParameters)
    (R₁ R₂ : Cell P.N → ℤ) (mask : Cell P.N → ℝ) (plen pre : ℕ) :
    0 ≤ conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask plen pre := by
  unfold conditionalPotential
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => columnPotential_nonneg R₁ R₂ mask _)
  · positivity

/-- `cor:conditional`, paper/paper.tex: the conditional potential
is the average of its two extensions by one seed bit. -/
theorem conditionalPotential_children {G₁ G₂ : ℕ} (P : SeedParameters)
    (R₁ R₂ : Cell P.N → ℤ) (mask : Cell P.N → ℝ) (plen pre : ℕ)
    (hplen : plen < seedLength P) :
    conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask plen pre =
      (conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask (plen+1) (pre % 2^plen) +
        conditionalPotential (G₁ := G₁) (G₂ := G₂) P R₁ R₂ mask (plen+1)
          (pre % 2^plen + 2^plen)) / 2 := by
  unfold conditionalPotential
  have hr : seedLength P-plen = (seedLength P-(plen+1))+1 := by omega
  rw [hr, pow_succ, mul_comm (2^(seedLength P-(plen+1))) 2,
    NearCubicWires.WireExponent3_5.Sampler.sum_range_two_mul]
  simp_rw [NearCubicWires.WireExponent3_5.Sampler.completion_split]
  field_simp
  ring

#print axioms conditionalPotential_children
#print axioms abs_scaledGamma_le
end NearQuarticWires.Cycle
