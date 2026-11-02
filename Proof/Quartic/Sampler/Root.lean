import Proof.Quartic.Sampler.SignedMoment

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open NearCubicWires.WireExponent3_5.Shared

/-- `lem:root`, paper/paper.tex: the concrete m=4 half potential. -/
noncomputable abbrev halfPotential {N Q : ℕ} {Z T : Type} [Fintype Z] [Fintype T]
    (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) : ℝ :=
  NearCubicWires.WireExponent3_5.Sampler.potential D S

/-- `lem:root`, paper/paper.tex: the actual paper dilation potential. -/
noncomputable def paperPotential {N Q : ℕ} {Z T : Type} [Fintype Z] [Fintype T]
    (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) : ℝ :=
  2 * halfPotential D S

/-- `lem:tracebound`, paper/paper.tex: the EXACT independent
uniform mean of the whole concrete paper potential, from the already-proved
signed direct walk bound (algorithm trace order four). -/
theorem mean_paperPotential_le {N Q : ℕ} {Z T : Type} [Fintype Z] [Fintype T]
    (hN : 1 ≤ N) (hNQ : N ≤ Q) (D : Z → T → Cell N → ℝ)
    (hD : ∀ z t c, |D z t c| ≤ 1) :
    uMean (fun S : Fin Q → Cell N => paperPotential D S) ≤
      2 * ((Fintype.card Z : ℝ) * Fintype.card T *
      NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13) := by
  have h := NearCubicWires.WireExponent3_5.Sampler.uMean_potential_le hN hNQ D hD
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [paperPotential, halfPotential, uMean, ← Finset.mul_sum,
    mul_div_assoc] using h2

/-- `lem:root`, paper/paper.tex: raised-power form of the paper's
sample budget implies the precise direct-walk sample guard, already for N≥2. -/
theorem paper_budget_implies_direct {N Q I : ℕ} (hN : 2 ≤ N) (η : ℝ)
    (hQ : (4096 : ℝ) ^ 4 * 4 * I * (N : ℝ) ^ 6 ≤ (Q : ℝ) ^ 4 * η ^ 8) :
    4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 * I * (N : ℝ) ^ 5 ≤
      (Q : ℝ) ^ 4 * η ^ 8 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 * I * (N : ℝ) ^ 5
      = (5 * 2 ^ 48 : ℝ) * I * (N : ℝ) ^ 5 := by
        norm_num [NearCubicWires.WireExponent3_5.Sampler.C8]
    _ ≤ ((4 : ℝ) * 2 ^ 48 * N) * I * (N : ℝ) ^ 5 := by
      have hc : (5 * 2 ^ 48 : ℝ) ≤ 4 * 2 ^ 48 * N := by nlinarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg I)) (by positivity)
    _ = (4096 : ℝ) ^ 4 * 4 * I * (N : ℝ) ^ 6 := by ring
    _ ≤ _ := hQ

/-- `lem:root`, paper/paper.tex: the original real fourth-root
sample policy entails its exact raised-power form; finite parameters may test
the latter by integer powers as specified at `sec:params`. -/
theorem paper_fourth_root_budget {N Q I : ℕ} (η : ℝ) (hη : 0 < η)
    (hQ : (4096 : ℝ) * N / η ^ 2 *
      ((4 : ℝ) * (N : ℝ) ^ 2 * I) ^ ((4 : ℝ)⁻¹) ≤ Q) :
    (4096 : ℝ) ^ 4 * 4 * I * (N : ℝ) ^ 6 ≤ (Q : ℝ) ^ 4 * η ^ 8 := by
  have hx : 0 ≤ (4 : ℝ) * (N : ℝ) ^ 2 * I := by positivity
  have hr : (((4 : ℝ) * (N : ℝ) ^ 2 * I) ^ ((4 : ℝ)⁻¹)) ^ 4 =
      (4 : ℝ) * (N : ℝ) ^ 2 * I :=
    Real.rpow_inv_natCast_pow hx (by norm_num : (4 : ℕ) ≠ 0)
  have h4 := pow_le_pow_left₀ (by positivity : 0 ≤ (4096 : ℝ) * N / η ^ 2 *
      ((4 : ℝ) * (N : ℝ) ^ 2 * I) ^ ((4 : ℝ)⁻¹)) hQ 4
  have heq : ((4096 : ℝ) * N / η ^ 2 *
      ((4 : ℝ) * (N : ℝ) ^ 2 * I) ^ ((4 : ℝ)⁻¹)) ^ 4 * η ^ 8 =
      (4096 : ℝ) ^ 4 * 4 * I * (N : ℝ) ^ 6 := by
    rw [mul_pow, hr]
    field_simp
  rw [← heq]
  exact mul_le_mul_of_nonneg_right h4 (by positivity)

/-- `lem:root`, paper/paper.tex, direct-moment realization:
one concrete paper-potential bound gives average error for EVERY signed matrix
index choice and EVERY pair of complex selectors, with no Tropp input. -/
theorem average_selector_error_of_paperPotential
    {N Q : ℕ} {Z T : Type} [Fintype Z] [Nonempty Z] [Fintype T]
    (hN : 1 ≤ N) (hNQ : N ≤ Q) (D : Z → T → Cell N → ℝ)
    (S : Fin Q → Cell N)
    (hS : paperPotential D S ≤ 2 * ((Fintype.card Z : ℝ) * Fintype.card T *
      NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13))
    (η : ℝ) (hη : 0 ≤ η)
    (hQη : 4 ^ 8 * NearCubicWires.WireExponent3_5.Sampler.C8 *
      Fintype.card T * (N : ℝ) ^ 5 ≤ (Q : ℝ) ^ 4 * η ^ 8)
    (τ : Z → T) (a b : Z → Fin N → ℂ)
    (ha : ∀ z i, ‖a z i‖ ≤ 1) (hb : ∀ z i, ‖b z i‖ ≤ 1) :
    (uMean fun z => ‖NearCubicWires.WireExponent3_5.Sampler.sampleErr
      (D z (τ z)) S (a z) (b z)‖) ≤ η := by
  apply NearCubicWires.WireExponent3_5.Sampler.universal_of_potential_le
    hN hNQ D S _ η hη hQη τ a b ha hb
  unfold paperPotential at hS
  linarith

/-- `lem:tracebound` and `lem:root`, paper/paper.tex:
the signed-matrix moment estimate gives a sample with the concrete paper potential bound. -/
theorem exists_paperPotential_le {N Q : ℕ} {Z T : Type} [Fintype Z] [Fintype T]
    (hN : 1 ≤ N) (hNQ : N ≤ Q) (D : Z → T → Cell N → ℝ)
    (hD : ∀ z t c, |D z t c| ≤ 1) :
    ∃ S : Fin Q → Cell N,
      paperPotential D S ≤ 2 * ((Fintype.card Z : ℝ) * Fintype.card T *
      NearCubicWires.WireExponent3_5.Sampler.C8 * (Q : ℝ) ^ 4 * (N : ℝ) ^ 13) := by
  obtain ⟨S, hS⟩ := NearCubicWires.WireExponent3_5.Sampler.exists_potential_le
    hN hNQ D hD
  exact ⟨S, mul_le_mul_of_nonneg_left hS (by norm_num)⟩

/-- `eq:ED` and `lem:root`, paper/paper.tex:
the degenerate N=1 case has zero error, regardless of the signed matrix entries. -/
theorem errorMatrix_one_eq_zero {Q : ℕ} (D : Cell 1 → ℝ)
    (S : Fin Q → Cell 1) : errorMatrix D S = 0 := by
  ext u v
  have heq : ∀ j, S j = (u, v) := fun j => Subsingleton.elim _ _
  simp [errorMatrix, NearCubicWires.WireExponent3_5.Sampler.errMatrix,
    Ecell, yc, heq]

end NearQuarticWires.Sampler
