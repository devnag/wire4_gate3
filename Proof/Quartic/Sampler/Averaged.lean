import Proof.Quartic.Sampler.Root
import Proof.Quartic.Sampler.Selector

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset Matrix
open NearCubicWires.WireExponent3_5.Shared

/-- `lem:selector`, paper/paper.tex: exact selected complex error. -/
noncomputable def complexSelectorError {N Q : ℕ} (M : Cell N → ℂ)
    (S : Fin Q → Cell N) (a b : Fin N → ℂ) : ℂ :=
  (∑ u, ∑ v, a u * b v * M (u, v)) / (N : ℂ) ^ 2 -
    (∑ j, a (S j).1 * b (S j).2 * M (S j)) / (Q : ℂ)

/-- `lem:selector`, paper/paper.tex: the exact complex error is
the sum of the two REAL-matrix errors used in the trace potential. -/
theorem complexSelectorError_re_im {N Q : ℕ} (M : Cell N → ℂ)
    (S : Fin Q → Cell N) (a b : Fin N → ℂ) :
    complexSelectorError M S a b =
      NearCubicWires.WireExponent3_5.Sampler.sampleErr (fun c => (M c).re) S a b +
      Complex.I * NearCubicWires.WireExponent3_5.Sampler.sampleErr
        (fun c => (M c).im) S a b := by
  have hfun : M = fun c => ((M c).re : ℂ) + Complex.I * ((M c).im : ℂ) := by
    funext c
    apply Complex.ext <;> simp
  conv_lhs => rw [hfun]
  unfold complexSelectorError NearCubicWires.WireExponent3_5.Sampler.sampleErr
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [add_div]
  have hfull : (∑ u, ∑ v, a u * b v * (Complex.I * ((M (u, v)).im : ℂ))) =
      Complex.I * ∑ u, ∑ v, a u * b v * ((M (u, v)).im : ℂ) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsample : (∑ j, a (S j).1 * b (S j).2 * (Complex.I * ((M (S j)).im : ℂ))) =
      Complex.I * ∑ j, a (S j).1 * b (S j).2 * ((M (S j)).im : ℂ) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfull, hsample]
  ring

/-- `lem:selector`, paper/paper.tex: exact linearity of the
selected Fourier row error, retaining all selector factors. -/
theorem selectedRow_error_identity {N Q : ℕ} {T : Type} [Fintype T]
    (c : T → ℂ) (a b : T → Fin N → ℂ) (M : T → Fin N → Fin N → ℂ)
    (S : Fin Q → Cell N) :
    complexSelectorError (fun x => selectedRow c a b M x.1 x.2) S
      (fun _ => 1) (fun _ => 1) =
    ∑ t, c t * complexSelectorError (fun x => M t x.1 x.2) S (a t) (b t) := by
  have hfull : (∑ u, ∑ v, selectedRow c a b M u v) =
      ∑ t, c t * ∑ u, ∑ v, a t u * b t v * M t u v := by
    simp only [selectedRow, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsample : (∑ j, selectedRow c a b M (S j).1 (S j).2) =
      ∑ t, c t * ∑ j, a t (S j).1 * b t (S j).2 * M t (S j).1 (S j).2 := by
    simp only [selectedRow, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold complexSelectorError
  simp only [one_mul]
  rw [hfull, hsample, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- `lem:root` + `lem:selector`, paper/paper.tex:
the ACTUAL potential controls average complex selector error with factor two.
No matrix-norm comparison between scalar fields or Tropp axiom is required. -/
theorem average_complexSelectorError_le {N Q : ℕ} {Z T : Type}
    [Fintype Z] [Nonempty Z] [Fintype T]
    (hN : 1 ≤ N) (hNQ : N ≤ Q) (M : Z → T → Cell N → ℂ)
    (S : Fin Q → Cell N)
    (D : Z → T × Fin 2 → Cell N → ℝ)
    (hD₀ : ∀ z t c, D z (t, 0) c = (M z t c).re)
    (hD₁ : ∀ z t c, D z (t, 1) c = (M z t c).im)
    (hS : paperPotential D S ≤ 2 * ((Fintype.card Z : ℝ) *
      Fintype.card (T × Fin 2) * NearCubicWires.WireExponent3_5.Sampler.C8 *
      (Q : ℝ) ^ 4 * (N : ℝ) ^ 13))
    (η : ℝ) (hη : 0 ≤ η)
    (hQη : 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 *
      Fintype.card (T × Fin 2) * (N : ℝ) ^ 5 ≤ (Q : ℝ) ^ 4 * η ^ 8)
    (τ : Z → T) (a b : Z → Fin N → ℂ)
    (ha : ∀ z i, ‖a z i‖ ≤ 1) (hb : ∀ z i, ‖b z i‖ ≤ 1) :
    (uMean fun z => ‖complexSelectorError (M z (τ z)) S (a z) (b z)‖) ≤ 2 * η := by
  have h₀ := average_selector_error_of_paperPotential hN hNQ D S hS η hη hQη
    (fun z => (τ z, 0)) a b ha hb
  have h₁ := average_selector_error_of_paperPotential hN hNQ D S hS η hη hQη
    (fun z => (τ z, 1)) a b ha hb
  have e₀ : ∀ z, D z (τ z, 0) = fun c => (M z (τ z) c).re := by
    intro z
    funext c
    exact hD₀ z (τ z) c
  have e₁ : ∀ z, D z (τ z, 1) = fun c => (M z (τ z) c).im := by
    intro z
    funext c
    exact hD₁ z (τ z) c
  simp_rw [e₀] at h₀
  simp_rw [e₁] at h₁
  have hpt : ∀ z, ‖complexSelectorError (M z (τ z)) S (a z) (b z)‖ ≤
      ‖NearCubicWires.WireExponent3_5.Sampler.sampleErr
        (fun c => (M z (τ z) c).re) S (a z) (b z)‖ +
      ‖NearCubicWires.WireExponent3_5.Sampler.sampleErr
        (fun c => (M z (τ z) c).im) S (a z) (b z)‖ := by
    intro z
    rw [complexSelectorError_re_im]
    simpa only [norm_mul, Complex.norm_I, one_mul] using norm_add_le
      (NearCubicWires.WireExponent3_5.Sampler.sampleErr
        (fun c => (M z (τ z) c).re) S (a z) (b z))
      (Complex.I * NearCubicWires.WireExponent3_5.Sampler.sampleErr
        (fun c => (M z (τ z) c).im) S (a z) (b z))
  exact (uMean_mono hpt).trans (by rw [uMean_add]; linarith)

/-- `lem:selector` + `lem:root`, paper/paper.tex: concrete
averaged Fourier-row error 2 M_F η directly from the signed trace potential.
This is the exact consumer used by soundness and requires no per-column choice
of numerical spectral eigenvectors or new matrix-concentration input. -/
theorem average_FourierRow_error {N Q : ℕ} {Z T Λ : Type}
    [Fintype Z] [Nonempty Z] [Fintype T] [Fintype Λ]
    (hN : 1 ≤ N) (hNQ : N ≤ Q) (M : Z → T → Cell N → ℂ)
    (S : Fin Q → Cell N) (D : Z → T × Fin 2 → Cell N → ℝ)
    (hD₀ : ∀ z t c, D z (t, 0) c = (M z t c).re)
    (hD₁ : ∀ z t c, D z (t, 1) c = (M z t c).im)
    (hS : paperPotential D S ≤ 2 * ((Fintype.card Z : ℝ) *
      Fintype.card (T × Fin 2) * NearCubicWires.WireExponent3_5.Sampler.C8 *
      (Q : ℝ) ^ 4 * (N : ℝ) ^ 13))
    (η MF : ℝ) (hη : 0 ≤ η)
    (hQη : 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 *
      Fintype.card (T × Fin 2) * (N : ℝ) ^ 5 ≤ (Q : ℝ) ^ 4 * η ^ 8)
    (π : Λ → T) (c : Λ → ℂ) (hmass : (∑ t, ‖c t‖) ≤ MF)
    (a b : Z → Λ → Fin N → ℂ)
    (ha : ∀ z t i, ‖a z t i‖ ≤ 1) (hb : ∀ z t i, ‖b z t i‖ ≤ 1) :
    (uMean fun z => ‖complexSelectorError
      (fun x => selectedRow c (a z) (b z) (fun t u v => M z (π t) (u, v)) x.1 x.2)
      S (fun _ => 1) (fun _ => 1)‖) ≤ 2 * MF * η := by
  have hmean : ∀ t, (uMean fun z => ‖complexSelectorError (M z (π t)) S
      (a z t) (b z t)‖) ≤ 2 * η := by
    intro t
    exact average_complexSelectorError_le hN hNQ M S D hD₀ hD₁ hS η hη hQη
      (fun _ => π t) (fun z => a z t) (fun z => b z t)
      (fun z => ha z t) (fun z => hb z t)
  simp_rw [selectedRow_error_identity]
  have hpt : ∀ z, ‖∑ t, c t * complexSelectorError (M z (π t)) S (a z t) (b z t)‖ ≤
      ∑ t, ‖c t‖ * ‖complexSelectorError (M z (π t)) S (a z t) (b z t)‖ := by
    intro z
    simpa only [norm_mul] using norm_sum_le
      Finset.univ (fun t => c t * complexSelectorError (M z (π t)) S (a z t) (b z t))
  refine (uMean_mono hpt).trans ?_
  have hswitch : (uMean fun z => ∑ t, ‖c t‖ *
      ‖complexSelectorError (M z (π t)) S (a z t) (b z t)‖) =
      ∑ t, ‖c t‖ * uMean (fun z => ‖complexSelectorError
        (M z (π t)) S (a z t) (b z t)‖) := by
    unfold uMean
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.mul_sum, mul_div_assoc]
  rw [hswitch]
  calc _ ≤ ∑ t, ‖c t‖ * (2 * η) := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left (hmean t) (norm_nonneg _)
    _ = (∑ t, ‖c t‖) * (2 * η) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2 * MF * η := by nlinarith

end NearQuarticWires.Sampler
