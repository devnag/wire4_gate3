import Proof.Quartic.Cycle.ComplexProduct
import Proof.Quartic.Cycle.PhaseProduct

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler

/-- Paper `lem:cycle`: κ has the same integer and complex coefficient. -/
theorem kappa_cast (m : ℕ) (σ : SignPattern m) :
    (kappa m σ : ℂ) =
      1 + (-1 : ℂ)^m * ∏ i, choiceSign (R := ℂ) (σ i) := by
  have hs (b : Bool) : (signValue b : ℂ) = choiceSign (R := ℂ) b := by
    cases b <;> simp [signValue, choiceSign]
  simp [kappa, hs]

/-- Paper `lem:cycle`: summing Re/Im products over the concrete two-score
character group detects the two signed integer residuals modulo their actual moduli. -/
theorem frequency_parts_sum {m G₁ G₂ : ℕ} (a b : Fin (2*m) → ℤ) :
    (4 : ℂ)^m * (∑ θ : Frequency m G₁ G₂,
      ((∏ i, (phase θ (a i) (b i)).re : ℂ) + ∏ i, (phase θ (a i) (b i)).im)) =
      (omega m G₁ : ℂ) * (omega m G₂ : ℂ) *
        ∑ σ : SignPattern m, (kappa m σ : ℂ) *
          (if ((∑ i, signValue (σ i) * a i : ℤ) : ZMod (omega m G₁)) = 0 then 1 else 0) *
          (if ((∑ i, signValue (σ i) * b i : ℤ) : ZMod (omega m G₂)) = 0 then 1 else 0) := by
  classical
  have hθ (θ : Frequency m G₁ G₂) :
      (4 : ℂ)^m * (((∏ i, (phase θ (a i) (b i)).re : ℂ) +
          ∏ i, (phase θ (a i) (b i)).im)) =
        ∑ σ : SignPattern m, (kappa m σ : ℂ) *
          phase θ (∑ i, signValue (σ i) * a i) (∑ i, signValue (σ i) * b i) := by
    rw [re_im_product]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← kappa_cast]
    congr 1
    simp_rw [phase_choice]
    exact (phase_finset_sum θ _ _ Finset.univ).symm
  rw [Finset.mul_sum]
  simp_rw [hθ]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_phase]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end NearQuarticWires.Cycle
