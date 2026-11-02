import Proof.Quartic.Sampler.Basic

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset
open NearCubicWires.WireExponent3_5.Rows

local notation "fc" => NearCubicWires.WireExponent3_5.Rows.fourierCoeff

section OneDimensional
variable {P : ℕ} [NeZero P]

/-- `lem:fourier`, paper/paper.tex: conjugation of a character. -/
theorem conj_chi (x : ZMod P) : star (chi x) = chi (-x) := by
  rw [show chi (-x) = (chi x)⁻¹ by
    exact AddChar.map_neg_eq_inv ZMod.stdAddChar x]
  exact (Complex.inv_eq_conj (norm_chi x)).symm

/-- `lem:fourier`, paper/paper.tex: conjugated normalized coefficient. -/
theorem conj_fourierCoeff (f : ZMod P → ℂ) (ℓ : ZMod P) :
    star (fc f ℓ) = (P : ℂ)⁻¹ *
      ∑ t : ZMod P, chi (t * ℓ) * star (f t) := by
  simp only [NearCubicWires.WireExponent3_5.Rows.fourierCoeff, star_mul, star_inv₀, star_natCast, star_sum, conj_chi,
    neg_neg]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_comm t ℓ]
  ring

/-- `lem:fourier`, paper/paper.tex: exact finite Parseval identity. -/
theorem parseval_cyclic (f : ZMod P → ℂ) :
    ∑ ℓ : ZMod P, ‖fc f ℓ‖ ^ 2 =
      (P : ℝ)⁻¹ * ∑ t : ZMod P, ‖f t‖ ^ 2 := by
  have hc : (∑ ℓ : ZMod P, fc f ℓ * star (fc f ℓ)) =
      (P : ℂ)⁻¹ * ∑ t : ZMod P, f t * star (f t) := by
    simp_rw [conj_fourierCoeff]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    calc (∑ ℓ : ZMod P, fc f ℓ * ((P : ℂ)⁻¹ *
        (chi (t * ℓ) * star (f t)))) =
        (P : ℂ)⁻¹ * (∑ ℓ : ZMod P, fc f ℓ * chi (ℓ * t)) * star (f t) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [mul_comm t ℓ]
          ring
      _ = _ := by rw [← fourier_inversion]; ring
  have hreal : (∑ ℓ : ZMod P, (‖fc f ℓ‖ ^ 2 : ℝ) : ℂ) =
      (((P : ℝ)⁻¹ * ∑ t : ZMod P, ‖f t‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    simpa only [← Complex.mul_conj', Complex.star_def] using hc
  exact_mod_cast hreal

end OneDimensional

section TwoDimensional
variable {P₁ P₂ : ℕ} [NeZero P₁] [NeZero P₂]

/-- `lem:fourier`, paper/paper.tex: the actual two-coordinate character. -/
noncomputable def groupChar (θ s : ZMod P₁ × ZMod P₂) : ℂ :=
  chi (θ.1 * s.1) * chi (θ.2 * s.2)

/-- `lem:fourier`, paper/paper.tex: the normalized two-score coefficients. -/
noncomputable def coefficient (F : ZMod P₁ × ZMod P₂ → ℂ)
    (θ : ZMod P₁ × ZMod P₂) : ℂ :=
  fc (fun t₁ => fc (fun t₂ => F (t₁, t₂)) θ.2) θ.1

/-- `lem:fourier`, paper/paper.tex: exact two-score inversion. -/
theorem product_fourier_inversion (F : ZMod P₁ × ZMod P₂ → ℂ)
    (s : ZMod P₁ × ZMod P₂) :
    F s = ∑ θ : ZMod P₁ × ZMod P₂, coefficient F θ * groupChar θ s := by
  rw [Fintype.sum_prod_type]
  calc F s = ∑ t₂ : ZMod P₂, fc (fun t₂ => F (s.1, t₂)) t₂ * chi (t₂ * s.2) :=
      by simpa only [Prod.mk.eta] using
        fourier_inversion (fun t₂ => F (s.1, t₂)) s.2
    _ = ∑ t₂ : ZMod P₂, (∑ t₁ : ZMod P₁,
        coefficient F (t₁, t₂) * chi (t₁ * s.1)) * chi (t₂ * s.2) := by
      apply Finset.sum_congr rfl
      intro t₂ _
      rw [show fc (fun t₂ => F (s.1, t₂)) t₂ =
        ∑ t₁ : ZMod P₁, coefficient F (t₁, t₂) * chi (t₁ * s.1) from
          fourier_inversion (fun t₁ => fc (fun t₂ => F (t₁, t₂)) t₂) s.1]
    _ = _ := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t₁ _
      apply Finset.sum_congr rfl
      intro t₂ _
      simp only [groupChar]
      ring

/-- `lem:fourier`, paper/paper.tex: exact product Parseval. -/
theorem product_parseval (F : ZMod P₁ × ZMod P₂ → ℂ) :
    ∑ θ : ZMod P₁ × ZMod P₂, ‖coefficient F θ‖ ^ 2 =
      ((P₁ : ℝ) * P₂)⁻¹ * ∑ s : ZMod P₁ × ZMod P₂, ‖F s‖ ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [coefficient]
  simp_rw [parseval_cyclic]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [parseval_cyclic]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_inv, Fintype.sum_prod_type]

/-- `lem:fourier`, paper/paper.tex: squared coefficient mass is at most one. -/
theorem coefficient_sq_mass_le (F : ZMod P₁ × ZMod P₂ → ℂ)
    (hF : ∀ s, ‖F s‖ ≤ 1) :
    ∑ θ : ZMod P₁ × ZMod P₂, ‖coefficient F θ‖ ^ 2 ≤ 1 := by
  rw [product_parseval]
  have hp : (0 : ℝ) < (P₁ : ℝ) * P₂ := by
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne P₁)))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne P₂)))
  rw [inv_mul_le_iff₀ hp, mul_one]
  calc (∑ s : ZMod P₁ × ZMod P₂, ‖F s‖ ^ 2) ≤
      ∑ _s : ZMod P₁ × ZMod P₂, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro s _
        nlinarith [hF s, norm_nonneg (F s)]
    _ = _ := by simp [ZMod.card]

/-- `lem:fourier`, paper/paper.tex: the sharp √|Θ| Fourier l1 bill. -/
theorem coefficient_mass_le (F : ZMod P₁ × ZMod P₂ → ℂ)
    (hF : ∀ s, ‖F s‖ ≤ 1) :
    ∑ θ : ZMod P₁ × ZMod P₂, ‖coefficient F θ‖ ≤
      Real.sqrt ((P₁ : ℝ) * P₂) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ZMod P₁ × ZMod P₂ => (1 : ℝ)) (fun θ => ‖coefficient F θ‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_prod, ZMod.card, Nat.cast_mul] at hcs
  have hmass := coefficient_sq_mass_le F hF
  have hp : (0 : ℝ) ≤ (P₁ : ℝ) * P₂ := by positivity
  have hsq : (∑ θ : ZMod P₁ × ZMod P₂, ‖coefficient F θ‖) ^ 2 ≤
      (P₁ : ℝ) * P₂ := hcs.trans (by nlinarith)
  nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg ((P₁ : ℝ) * P₂),
    Finset.sum_nonneg (s := Finset.univ) (fun θ _ => norm_nonneg (coefficient F θ))]

end TwoDimensional

section ConcreteScore
variable {m G₁ G₂ N : ℕ}

/-- `lem:fourier`, paper/paper.tex: exact masked Fourier row for
the actual integer left/right/residual score split. The modulus is 4mG+1. -/
theorem masked_score_decomposition (F : Frequency m G₁ G₂ → ℂ)
    (L₁ L₂ R₁ R₂ : Fin N → ℤ) (D₁ D₂ : Cell N → ℤ)
    (mask : Cell N → ℝ) (u v : Fin N) :
    F (((L₁ u + R₁ v + D₁ (u, v) : ℤ) : ZMod (omega m G₁)),
        ((L₂ u + R₂ v + D₂ (u, v) : ℤ) : ZMod (omega m G₂))) * (mask (u, v) : ℂ) =
      ∑ θ : Frequency m G₁ G₂, coefficient F θ * phase θ (L₁ u) (L₂ u) *
        phase θ (R₁ v) (R₂ v) * maskedPhase θ D₁ D₂ mask (u, v) := by
  rw [product_fourier_inversion F, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro θ _
  have hp : groupChar θ
      (((L₁ u + R₁ v + D₁ (u, v) : ℤ) : ZMod (omega m G₁)),
       ((L₂ u + R₂ v + D₂ (u, v) : ℤ) : ZMod (omega m G₂))) =
      phase θ (L₁ u + R₁ v + D₁ (u, v)) (L₂ u + R₂ v + D₂ (u, v)) := rfl
  rw [hp, phase_add, phase_add]
  unfold maskedPhase
  ring

/-- `lem:fourier`, paper/paper.tex: the concrete selectors are unimodular. -/
theorem score_selector_norm (θ : Frequency m G₁ G₂) (L₁ L₂ : Fin N → ℤ)
    (u : Fin N) : ‖phase θ (L₁ u) (L₂ u)‖ ≤ 1 := by
  rw [norm_phase]

/-- `lem:fourier`, paper/paper.tex: a full explicit integer Fourier
mass bound M_F is valid whenever M_F²≥|Θ| (no real-valued ceiling oracle). -/
theorem coefficient_mass_le_integer (F : Frequency m G₁ G₂ → ℂ)
    (hF : ∀ s, ‖F s‖ ≤ 1) (MF : ℕ)
    (hMF : omega m G₁ * omega m G₂ ≤ MF ^ 2) :
    ∑ θ : Frequency m G₁ G₂, ‖coefficient F θ‖ ≤ MF := by
  have h := coefficient_mass_le F hF
  have hcast : (omega m G₁ : ℝ) * omega m G₂ ≤ (MF : ℝ) ^ 2 := by
    exact_mod_cast hMF
  have hs : Real.sqrt ((omega m G₁ : ℝ) * omega m G₂) ≤ MF := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg MF)]
    exact Real.sqrt_le_sqrt hcast
  exact h.trans hs

end ConcreteScore

end NearQuarticWires.Sampler
