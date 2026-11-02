import Proof.Quartic.Cycle.TracePotential
import Proof.Quartic.Cycle.WalkFrequency

set_option autoImplicit false

namespace NearQuarticWires.Cycle
open Finset
open NearQuarticWires.Sampler

/-- Paper `lem:cycle`: the concrete m=4 potential as signed masked phase products. -/
theorem columnPotential_phase_parts {N Q G₁ G₂ : ℕ}
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (S : Fin Q → Cell N) :
    columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
      2 * ∑ w : Walk N 4,
        walkGamma (by norm_num) S w * walkMask (by norm_num) mask w *
          ∑ θ : Frequency 4 G₁ G₂,
            ((∏ l, (phase θ (R₁ (edge (by norm_num) w l))
              (R₂ (edge (by norm_num) w l))).re) +
              ∏ l, (phase θ (R₁ (edge (by norm_num) w l))
                (R₂ (edge (by norm_num) w l))).im) := by
  classical
  rw [columnPotential_walks]
  congr 1
  calc
    (∑ θ : Frequency 4 G₁ G₂, ∑ ν : Fin 2, ∑ w : Walk N 4,
        ∏ l, (realPartMatrix θ R₁ R₂ mask ν (edge (by norm_num) w l) *
          gamma S (edge (by norm_num) w l))) =
        ∑ θ : Frequency 4 G₁ G₂, ∑ w : Walk N 4, ∑ ν : Fin 2,
          ∏ l, (realPartMatrix θ R₁ R₂ mask ν (edge (by norm_num) w l) *
            gamma S (edge (by norm_num) w l)) := by
      apply Finset.sum_congr rfl
      intro θ _
      exact Finset.sum_comm
    _ = ∑ w : Walk N 4, ∑ θ : Frequency 4 G₁ G₂, ∑ ν : Fin 2,
          ∏ l, (realPartMatrix θ R₁ R₂ mask ν (edge (by norm_num) w l) *
            gamma S (edge (by norm_num) w l)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      simp_rw [walk_parts_sum]
      rw [← Finset.mul_sum]

/-- Paper `lem:cycle`: the FULL concrete cycle-sum identity at the paper's m=4.
It includes signed Γ_w, the SAME mask in every frequency, the exact κσ,
and INTEGER vanishing of BOTH residual walk sums. -/
theorem cycle_sum_identity {N Q G₁ G₂ : ℕ}
    (R₁ R₂ : Cell N → ℤ) (mask : Cell N → ℝ) (S : Fin Q → Cell N)
    (hR₁ : ∀ c, |R₁ c| ≤ G₁) (hR₂ : ∀ c, |R₂ c| ≤ G₂) :
    columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
      (2 * (Fintype.card (Frequency 4 G₁ G₂) : ℝ) / (4 : ℝ)^4) *
        ∑ w : Walk N 4, walkGamma (by norm_num) S w * walkMask (by norm_num) mask w *
          ∑ σ : SignPattern 4, (kappa 4 σ : ℝ) *
            (if walkSum (by norm_num) R₁ σ w = 0 then 1 else 0) *
            (if walkSum (by norm_num) R₂ σ w = 0 then 1 else 0) := by
  classical
  let C : Walk N 4 → ℝ := fun w => walkGamma (by norm_num) S w * walkMask (by norm_num) mask w
  let P : Walk N 4 → ℝ := fun w => ∑ θ : Frequency 4 G₁ G₂,
    ((∏ l, (phase θ (R₁ (edge (by norm_num) w l)) (R₂ (edge (by norm_num) w l))).re) +
      ∏ l, (phase θ (R₁ (edge (by norm_num) w l)) (R₂ (edge (by norm_num) w l))).im)
  let W : Walk N 4 → ℝ := fun w => ∑ σ : SignPattern 4, (kappa 4 σ : ℝ) *
    (if walkSum (by norm_num) R₁ σ w = 0 then 1 else 0) *
    (if walkSum (by norm_num) R₂ σ w = 0 then 1 else 0)
  have hP (w : Walk N 4) : (4 : ℝ)^4 * P w =
      (omega 4 G₁ : ℝ) * (omega 4 G₂ : ℝ) * W w :=
    walk_frequency_parts (by norm_num) R₁ R₂ hR₁ hR₂ w
  have hcol : columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
      2 * ∑ w, C w * P w := columnPotential_phase_parts R₁ R₂ mask S
  have hmain : (4 : ℝ)^4 * columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
      2 * (omega 4 G₁ : ℝ) * (omega 4 G₂ : ℝ) * ∑ w, C w * W w := by
    rw [hcol]
    calc
      (4 : ℝ)^4 * (2 * ∑ w, C w * P w) =
          2 * ∑ w, C w * ((4 : ℝ)^4 * P w) := by
        simp only [Finset.mul_sum]
        ring
      _ = 2 * ∑ w, C w * ((omega 4 G₁ : ℝ) * (omega 4 G₂ : ℝ) * W w) := by
        simp_rw [hP]
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        ring
  have hcard : (Fintype.card (Frequency 4 G₁ G₂) : ℝ) =
      (omega 4 G₁ : ℝ) * (omega 4 G₂ : ℝ) := by
    simp [Frequency, Fintype.card_prod, ZMod.card]
  change columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S =
    (2 * (Fintype.card (Frequency 4 G₁ G₂) : ℝ) / (4 : ℝ)^4) * ∑ w, C w * W w
  rw [hcard, div_mul_eq_mul_div]
  apply (eq_div_iff (by norm_num : (4 : ℝ)^4 ≠ 0)).2
  calc
    _ = (4 : ℝ)^4 * columnPotential (G₁ := G₁) (G₂ := G₂) R₁ R₂ mask S := mul_comm _ _
    _ = 2 * (omega 4 G₁ : ℝ) * (omega 4 G₂ : ℝ) * ∑ w, C w * W w := hmain
    _ = _ := by ring

#print axioms cycle_sum_identity
end NearQuarticWires.Cycle
