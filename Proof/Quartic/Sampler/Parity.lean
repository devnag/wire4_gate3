import Proof.Quartic.Sampler.Fourier

set_option autoImplicit false

namespace NearQuarticWires.Sampler

open Finset

/-- `lem:fourier`, paper/paper.tex: the two parity-call coefficient rows. -/
noncomputable def parityCoefficient {m G₁ G₂ : ℕ}
    (F : Frequency m G₁ G₂ → ℂ) (t : Frequency m G₁ G₂ × Fin 2) : ℂ :=
  if t.2 = 0 then (if t.1 = 0 then (1 / 2 : ℂ) else 0)
  else -(1 / 2 : ℂ) * coefficient F t.1

/-- `lem:fourier`, paper/paper.tex: parity modifies only selectors. -/
noncomputable def paritySelector {m G₁ G₂ N : ℕ}
    (χ : Fin N → ℂ) (L₁ L₂ : Fin N → ℤ)
    (t : Frequency m G₁ G₂ × Fin 2) (u : Fin N) : ℂ :=
  if t.2 = 0 then 1 else χ u * phase t.1 (L₁ u) (L₂ u)

/-- `lem:fourier`, paper/paper.tex:
the ACTUAL parity-call selectors have modulus at most one. -/
theorem paritySelector_norm {m G₁ G₂ N : ℕ}
    (χ : Fin N → ℂ) (hχ : ∀ u, ‖χ u‖ ≤ 1) (L₁ L₂ : Fin N → ℤ)
    (t : Frequency m G₁ G₂ × Fin 2) (u : Fin N) :
    ‖paritySelector χ L₁ L₂ t u‖ ≤ 1 := by
  unfold paritySelector
  split_ifs
  · simp
  · simpa only [norm_mul, norm_phase, mul_one] using hχ u

/-- `lem:fourier`, paper/paper.tex: the parity-call mass still
fits the SAME integer M_F as single and pair calls. -/
theorem parityCoefficient_mass_le {m G₁ G₂ : ℕ}
    (F : Frequency m G₁ G₂ → ℂ) (hF : ∀ s, ‖F s‖ ≤ 1)
    (MF : ℕ) (hMF : omega m G₁ * omega m G₂ ≤ MF ^ 2) :
    ∑ t : Frequency m G₁ G₂ × Fin 2, ‖parityCoefficient F t‖ ≤ MF := by
  classical
  have hmass := coefficient_mass_le_integer F hF MF hMF
  have hMFpos : 1 ≤ MF := by
    have hprod : 0 < omega m G₁ * omega m G₂ := by unfold omega; positivity
    by_contra h
    have : MF = 0 := by omega
    subst MF
    exact (Nat.not_lt_of_ge (show omega m G₁ * omega m G₂ ≤ 0 from hMF)) hprod
  have hMFreal : (1 : ℝ) ≤ MF := by exact_mod_cast hMFpos
  have hsplit : (∑ t : Frequency m G₁ G₂ × Fin 2, ‖parityCoefficient F t‖) =
      (1 / 2 : ℝ) + (1 / 2 : ℝ) * ∑ θ, ‖coefficient F θ‖ := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    have hterm : ∀ θ : Frequency m G₁ G₂,
        ‖parityCoefficient F (θ, 0)‖ + ‖parityCoefficient F (θ, 1)‖ =
        (if θ = 0 then (1 / 2 : ℝ) else 0) + (1 / 2 : ℝ) * ‖coefficient F θ‖ := by
      intro θ
      by_cases hθ : θ = 0 <;> simp [parityCoefficient, hθ]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  rw [hsplit]
  nlinarith

/-- `lem:fourier`, paper/paper.tex: the exact Boolean XOR identity,
including zero/one endpoints, before inserting the Fourier expansion. -/
theorem xor_bit_identity (g p : Bool) :
    (if Bool.xor g p then (1 : ℂ) else 0) = (1 / 2 : ℂ) - (1 / 2 : ℂ) *
      (if g then (-1 : ℂ) else 1) * (if p then (-1 : ℂ) else 1) := by
  cases g <;> cases p <;> norm_num

/-- `lem:fourier`, paper/paper.tex: exact parity-call Fourier
decomposition, with the mask inside the residual matrix and parity ONLY in the
two selectors. The left factor may include the column's constant parity sign. -/
theorem parity_masked_score_decomposition {m G₁ G₂ N : ℕ}
    (F : Frequency m G₁ G₂ → ℂ) (χL χR : Fin N → ℂ)
    (L₁ L₂ R₁ R₂ : Fin N → ℤ) (D₁ D₂ : Cell N → ℤ)
    (mask : Cell N → ℝ) (u v : Fin N) :
    (1 / 2 : ℂ) * (mask (u, v) : ℂ) - (1 / 2 : ℂ) * χL u * χR v *
      F (((L₁ u + R₁ v + D₁ (u, v) : ℤ) : ZMod (omega m G₁)),
         ((L₂ u + R₂ v + D₂ (u, v) : ℤ) : ZMod (omega m G₂))) *
      (mask (u, v) : ℂ) =
    ∑ t : Frequency m G₁ G₂ × Fin 2,
      parityCoefficient F t * paritySelector χL L₁ L₂ t u *
      paritySelector χR R₁ R₂ t v * maskedPhase t.1 D₁ D₂ mask (u, v) := by
  classical
  let C : Frequency m G₁ G₂ → ℂ := fun θ => coefficient F θ *
    phase θ (L₁ u) (L₂ u) * phase θ (R₁ v) (R₂ v) *
    maskedPhase θ D₁ D₂ mask (u, v)
  have hexp := masked_score_decomposition F L₁ L₂ R₁ R₂ D₁ D₂ mask u v
  change _ = ∑ θ, C θ at hexp
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have hterm : ∀ θ : Frequency m G₁ G₂,
      parityCoefficient F (θ, 0) * paritySelector χL L₁ L₂ (θ, 0) u *
        paritySelector χR R₁ R₂ (θ, 0) v * maskedPhase θ D₁ D₂ mask (u, v) +
      parityCoefficient F (θ, 1) * paritySelector χL L₁ L₂ (θ, 1) u *
        paritySelector χR R₁ R₂ (θ, 1) v * maskedPhase θ D₁ D₂ mask (u, v) =
      (if θ = 0 then (1 / 2 : ℂ) * (mask (u, v) : ℂ) else 0) -
        ((1 / 2 : ℂ) * χL u * χR v) * C θ := by
    intro θ
    by_cases hθ : θ = 0
    · subst θ
      simp [parityCoefficient, paritySelector, C, maskedPhase]
      ring
    · simp [parityCoefficient, paritySelector, hθ, C]
      ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← hexp]
  ring

end NearQuarticWires.Sampler
