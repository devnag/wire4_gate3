import Proof.Quartic.Sampler.Averaged
import Proof.Quartic.Sampler.CycleDock

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:selector`, paper/paper.tex: the actual real averaging error. -/
noncomputable def averagingError {N Q : ℕ} (f : Cell N → ℝ)
    (S : Fin Q → Cell N) : ℝ :=
  (∑ u, ∑ v, f (u, v)) / (N : ℝ) ^ 2 - (∑ j, f (S j)) / (Q : ℝ)

/-- `lem:selector`, paper/paper.tex: exact real/complex error agreement. -/
theorem complexSelectorError_real {N Q : ℕ} (f : Cell N → ℝ)
    (S : Fin Q → Cell N) :
    complexSelectorError (fun x => (f x : ℂ)) S (fun _ => 1) (fun _ => 1) =
      (averagingError f S : ℂ) := by
  unfold complexSelectorError averagingError
  push_cast
  simp

/-- `lem:selector`, paper/paper.tex: the concrete masked-mass
error averaged over columns is ≤η, on the SAME actual dictionary/potential as Cycle. -/
theorem average_mask_error {N Q G₁ G₂ : ℕ} {Z : Type}
    [Fintype Z] [Nonempty Z] (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (R₁ R₂ : Z → Cell N → ℤ) (mask : Z → Cell N → ℝ)
    (S : Fin Q → Cell N)
    (hS : paperPotential (matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask) S ≤
      2 * ((Fintype.card Z : ℝ) * Fintype.card (Frequency 4 G₁ G₂ × Fin 2) *
      NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13))
    (η : ℝ) (hη : 0 ≤ η)
    (hQη : 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 *
      Fintype.card (Frequency 4 G₁ G₂ × Fin 2) * (N : ℝ) ^ 5 ≤
        (Q : ℝ) ^ 4 * η ^ 8) :
    (uMean fun z => |averagingError (mask z) S|) ≤ η := by
  have h := average_selector_error_of_paperPotential hN hNQ
    (matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask) S hS η hη hQη
    (fun _ => (0, 0)) (fun _ _ => 1) (fun _ _ => 1)
    (by intros; simp) (by intros; simp)
  have hzero : ∀ z, matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask z (0, 0) = mask z := by
    intro z
    funext c
    simp [matrixDictionary, maskedPhase]
  simp_rw [hzero] at h
  have heq : ∀ z, NearCubicWires.WireExponent3_5.Sampler.sampleErr
      (mask z) S (fun _ => 1) (fun _ => 1) = (averagingError (mask z) S : ℂ) := by
    intro z
    simpa only [complexSelectorError, NearCubicWires.WireExponent3_5.Sampler.sampleErr]
      using complexSelectorError_real (mask z) S
  simp_rw [heq, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- `lem:selector` + `lem:root`, paper/paper.tex: the actual
masked-predicate error is ≤2 M_F η on average over the certified columns.
The pointwise row identity is exactly the output of `lem:fourier`; the SAME
concrete Re/Im dictionary and Cycle potential serve single, pair and parity rows. -/
theorem average_masked_predicate_error {N Q G₁ G₂ : ℕ} {Z Λ : Type}
    [Fintype Z] [Nonempty Z] [Fintype Λ]
    (hN : 1 ≤ N) (hNQ : N ≤ Q)
    (R₁ R₂ : Z → Cell N → ℤ) (mask pred : Z → Cell N → ℝ)
    (S : Fin Q → Cell N)
    (hS : paperPotential (matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask) S ≤
      2 * ((Fintype.card Z : ℝ) * Fintype.card (Frequency 4 G₁ G₂ × Fin 2) *
      NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13))
    (η MF : ℝ) (hη : 0 ≤ η)
    (hQη : 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 *
      Fintype.card (Frequency 4 G₁ G₂ × Fin 2) * (N : ℝ) ^ 5 ≤
        (Q : ℝ) ^ 4 * η ^ 8)
    (π : Λ → Frequency 4 G₁ G₂) (coeff : Λ → ℂ)
    (hmass : (∑ t, ‖coeff t‖) ≤ MF)
    (a b : Z → Λ → Fin N → ℂ)
    (ha : ∀ z t i, ‖a z t i‖ ≤ 1) (hb : ∀ z t i, ‖b z t i‖ ≤ 1)
    (hrow : ∀ z u v, ((pred z (u, v) * mask z (u, v) : ℝ) : ℂ) =
      selectedRow coeff (a z) (b z)
        (fun t u v => maskedPhase (π t) (R₁ z) (R₂ z) (mask z) (u, v)) u v) :
    (uMean fun z => |averagingError (fun x => pred z x * mask z x) S|) ≤
      2 * MF * η := by
  have h := average_FourierRow_error hN hNQ
    (fun z θ => maskedPhase θ (R₁ z) (R₂ z) (mask z)) S
    (matrixDictionary (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask)
    (by intros; simp [matrixDictionary]) (by intros; simp [matrixDictionary])
    hS η MF hη hQη π coeff hmass a b ha hb
  have hfun : ∀ z, (fun x => selectedRow coeff (a z) (b z)
      (fun t u v => maskedPhase (π t) (R₁ z) (R₂ z) (mask z) (u, v)) x.1 x.2) =
      fun x => ((pred z x * mask z x : ℝ) : ℂ) := by
    intro z
    funext x
    exact (hrow z x.1 x.2).symm
  simp_rw [hfun, complexSelectorError_real, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end NearQuarticWires.Sampler
