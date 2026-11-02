import Proof.Quartic.Sampler.Fourier

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset Matrix
open NearCubicWires.WireExponent3_5.Shared
open scoped Matrix.Norms.L2Operator

/-- `lem:selector`, paper/paper.tex: E is additive in the matrix. -/
theorem sampleError_add {N Q : ℕ} (A B : Fin N → Fin N → ℂ)
    (S : Fin Q → Cell N) :
    sampleError (fun u v => A u v + B u v) S = sampleError A S + sampleError B S := by
  ext u v
  simp only [sampleError, Matrix.of_apply, Matrix.add_apply, mul_add]
  have hs : (∑ j, if S j = (u, v) then A u v + B u v else 0) =
      (∑ j, if S j = (u, v) then A u v else 0) +
      (∑ j, if S j = (u, v) then B u v else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hs]
  ring

/-- `lem:selector`, paper/paper.tex: E respects a complex scalar. -/
theorem sampleError_smul {N Q : ℕ} (c : ℂ) (A : Fin N → Fin N → ℂ)
    (S : Fin Q → Cell N) :
    sampleError (fun u v => c * A u v) S = c • sampleError A S := by
  ext u v
  simp only [sampleError, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hs : (∑ j, if S j = (u, v) then c * A u v else 0) =
      c * (∑ j, if S j = (u, v) then A u v else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hs]
  ring

/-- `lem:selector`, paper/paper.tex: concrete Re/Im error splitting. -/
theorem sampleError_re_im {N Q : ℕ} (M : Fin N → Fin N → ℂ)
    (S : Fin Q → Cell N) :
    sampleError M S = sampleError (fun u v => ((M u v).re : ℂ)) S +
      Complex.I • sampleError (fun u v => ((M u v).im : ℂ)) S := by
  rw [← sampleError_smul, ← sampleError_add]
  congr 1
  funext u v
  apply Complex.ext <;> simp

/-- `lem:selector`, paper/paper.tex: two real error bounds give
the exact factor two for the complex masked residual row. -/
theorem complex_error_le_two {N Q : ℕ} (M : Fin N → Fin N → ℂ)
    (S : Fin Q → Cell N) (ε : ℝ)
    (hε₀ : ‖sampleError (fun u v => ((M u v).re : ℂ)) S‖ / (Q * N) ≤ ε)
    (hε₁ : ‖sampleError (fun u v => ((M u v).im : ℂ)) S‖ / (Q * N) ≤ ε) :
    ‖sampleError M S‖ / (Q * N) ≤ 2 * ε := by
  rw [sampleError_re_im]
  have h := norm_add_le
    (sampleError (fun u v => ((M u v).re : ℂ)) S)
    (Complex.I • sampleError (fun u v => ((M u v).im : ℂ)) S)
  simp only [norm_smul, Complex.norm_I, one_mul] at h
  calc _ ≤ (‖sampleError (fun u v => ((M u v).re : ℂ)) S‖ +
      ‖sampleError (fun u v => ((M u v).im : ℂ)) S‖) / (Q * N) :=
        div_le_div_of_nonneg_right h (by positivity)
    _ ≤ 2 * ε := by rw [add_div]; linarith

/-- `lem:selector`, paper/paper.tex: the actual selected row. -/
noncomputable def selectedRow {N : ℕ} {T : Type} [Fintype T]
    (c : T → ℂ) (a b : T → Fin N → ℂ) (M : T → Fin N → Fin N → ℂ)
    (u v : Fin N) : ℂ := ∑ t, c t * a t u * b t v * M t u v

/-- `lem:selector`, paper/paper.tex: Fourier mass multiplies
uniform selector error, on the ACTUAL selected matrices (mask already inside). -/
theorem selectedRow_error {N Q : ℕ} {T : Type} [Fintype T]
    (hN : 0 < N) (hQ : 0 < Q)
    (c : T → ℂ) (a b : T → Fin N → ℂ) (M : T → Fin N → Fin N → ℂ)
    (ha : ∀ t i, ‖a t i‖ ≤ 1) (hb : ∀ t i, ‖b t i‖ ≤ 1)
    (S : Fin Q → Cell N) (ε : ℝ)
    (hε : ∀ t, ‖sampleError (M t) S‖ / (Q * N) ≤ ε) :
    ‖(∑ u, ∑ v, selectedRow c a b M u v) / (N : ℂ) ^ 2 -
      (∑ j, selectedRow c a b M (S j).1 (S j).2) / (Q : ℂ)‖ ≤
        (∑ t, ‖c t‖) * ε := by
  have hexpand : ∀ t, ‖(∑ u, a t u * (Matrix.of (M t) *ᵥ b t) u) /
      (N : ℂ)^2 - (∑ j, a t (S j).1 * b t (S j).2 *
      M t (S j).1 (S j).2) / (Q : ℂ)‖ ≤ ε := by
    intro t
    exact (sample_estimate_error hN hQ (M t) S (a t) (b t)
      (ha t) (hb t)).trans (hε t)
  have hfull : (∑ u, ∑ v, selectedRow c a b M u v) =
      ∑ t, c t * ∑ u, a t u * (Matrix.of (M t) *ᵥ b t) u := by
    simp only [selectedRow, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Finset.mul_sum]
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
  rw [hfull, hsample, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc ‖∑ t, (c t * (∑ u, a t u * (Matrix.of (M t) *ᵥ b t) u) /
      (N : ℂ)^2 - c t * (∑ j, a t (S j).1 * b t (S j).2 *
      M t (S j).1 (S j).2) / (Q : ℂ))‖ ≤
      ∑ t, ‖c t‖ * ε := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro t _
        rw [show c t * (∑ u, a t u * (Matrix.of (M t) *ᵥ b t) u) /
          (N : ℂ)^2 - c t * (∑ j, a t (S j).1 * b t (S j).2 *
          M t (S j).1 (S j).2) / (Q : ℂ) = c t *
          ((∑ u, a t u * (Matrix.of (M t) *ᵥ b t) u) / (N : ℂ)^2 -
          (∑ j, a t (S j).1 * b t (S j).2 * M t (S j).1 (S j).2) /
          (Q : ℂ)) by ring, norm_mul]
        exact mul_le_mul_of_nonneg_left (hexpand t) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- `lem:selector`, paper/paper.tex: the concrete 2 M_F bound,
with both real/imaginary sample-error matrices and full Fourier mass paid. -/
theorem selectedRow_error_two_parts {N Q : ℕ} {T : Type} [Fintype T]
    (hN : 0 < N) (hQ : 0 < Q)
    (c : T → ℂ) (a b : T → Fin N → ℂ) (M : T → Fin N → Fin N → ℂ)
    (ha : ∀ t i, ‖a t i‖ ≤ 1) (hb : ∀ t i, ‖b t i‖ ≤ 1)
    (S : Fin Q → Cell N) (ε MF : ℝ) (hε : 0 ≤ ε)
    (hmass : (∑ t, ‖c t‖) ≤ MF)
    (hε₀ : ∀ t, ‖sampleError (fun u v => ((M t u v).re : ℂ)) S‖ / (Q * N) ≤ ε)
    (hε₁ : ∀ t, ‖sampleError (fun u v => ((M t u v).im : ℂ)) S‖ / (Q * N) ≤ ε) :
    ‖(∑ u, ∑ v, selectedRow c a b M u v) / (N : ℂ) ^ 2 -
      (∑ j, selectedRow c a b M (S j).1 (S j).2) / (Q : ℂ)‖ ≤ 2 * MF * ε := by
  have h := selectedRow_error hN hQ c a b M ha hb S (2 * ε)
    (fun t => complex_error_le_two (M t) S ε (hε₀ t) (hε₁ t))
  refine h.trans ?_
  nlinarith

end NearQuarticWires.Sampler
