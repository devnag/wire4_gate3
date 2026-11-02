import Proof.Quartic.Mask.Structural
import Proof.Wire_3_5.StarPopulation

set_option autoImplicit false

namespace NearQuarticWires.Mask

open scoped BigOperators
open Finset NearCubicWires.WireExponent3_5.Shared

/-- Paper `lem:smaskmass`: the actual star-pattern count
of patterns hitting a fixed coordinate set, using the proved
`StarParams.card_errors_fixed` and injective physical block coordinates. -/
theorem star_hit_card_le (P : StarParams) (side : Fin (P.r / 2) → Fin P.r)
    (hside : Function.Injective side) (H : Finset (Fin P.n)) :
    (univ.filter fun u : P.Errors => ¬ Disjoint (P.flipSet side u) H).card ≤
      (P.b + 1) ^ (P.r / 2 - 1) * H.card := by
  classical
  let g : Fin (P.r / 2) × Fin P.b → Fin P.n :=
    fun p => P.blockCoord (side p.1) p.2
  have hg : Function.Injective g := P.coordPair_inj side hside
  let R : Finset (Fin (P.r / 2) × Fin P.b) := univ.filter fun p => g p ∈ H
  have hsub : (univ.filter fun u : P.Errors => ¬ Disjoint (P.flipSet side u) H) ⊆
      R.biUnion (fun p => univ.filter fun u : P.Errors => u p.1 = some p.2) := by
    intro u hu
    have hhit : ∃ x, x ∈ P.flipSet side u ∧ x ∈ H := by
      simpa only [mem_filter, mem_univ, true_and, Finset.not_disjoint_iff] using hu
    obtain ⟨x, hx, hxH⟩ := hhit
    obtain ⟨j, i, hji, hxi⟩ := (P.mem_flipSet side u x).mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨(j, i), ?_, by simp [hji]⟩
    simpa [R, g, hxi] using hxH
  have hR : R.card ≤ H.card := by
    apply Finset.card_le_card_of_injOn g
    · intro p hp
      exact (mem_filter.mp hp).2
    · intro p _ q _ hpq
      exact hg hpq
  calc
    _ ≤ (R.biUnion fun p => univ.filter fun u : P.Errors =>
        u p.1 = some p.2).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ R, (univ.filter fun u : P.Errors => u p.1 = some p.2).card :=
      Finset.card_biUnion_le
    _ = R.card * (P.b + 1) ^ (P.r / 2 - 1) := by
      simp [P.card_errors_fixed]
    _ ≤ _ := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hR

/-- Paper `lem:smaskmass`: left and right patterns are chosen
independently under the original uniform product law, so the discarded-pair
count is the product of the two actual one-pattern counts. -/
theorem structural_bad_pair_card (P : StarParams) (H : Finset (Fin P.n)) :
    (univ.filter fun uv : P.Errors × P.Errors =>
      structuralMask (P.flipSet P.leftBlock) (P.flipSet P.rightBlock) H
        uv.1 uv.2 = false).card =
      (univ.filter fun u : P.Errors => ¬ Disjoint (P.flipSet P.leftBlock u) H).card *
      (univ.filter fun v : P.Errors => ¬ Disjoint (P.flipSet P.rightBlock v) H).card := by
  classical
  rw [← Finset.card_product]
  congr 1
  ext uv
  simp [structuralMask]

/-- Paper `lem:smaskmass`: the complete structural-mask
mass estimate under the actual original uniform star-product law. All
coordinate probabilities and the independence factor are proved here from
the concrete star-pattern type, rather than supplied as hypotheses. -/
theorem structural_mask_mass (P : StarParams) (degree : Fin P.n → ℕ)
    (dstar W : ℕ) (hd : 0 < dstar) (hW : ∑ i, degree i ≤ W) :
    ((univ.filter fun uv : P.Errors × P.Errors =>
      structuralMask (P.flipSet P.leftBlock) (P.flipSet P.rightBlock)
        (heavyCoordinates degree dstar) uv.1 uv.2 = false).card : ℝ) /
      (Fintype.card P.Errors : ℝ) ^ 2 ≤
        ((W : ℝ) / ((dstar : ℝ) * ((P.b : ℝ) + 1))) ^ 2 := by
  classical
  let H := heavyCoordinates degree dstar
  let L := (univ.filter fun u : P.Errors => ¬ Disjoint (P.flipSet P.leftBlock u) H).card
  let R := (univ.filter fun v : P.Errors => ¬ Disjoint (P.flipSet P.rightBlock v) H).card
  have hh : 1 ≤ P.r / 2 := by have := P.two_le_r; omega
  have hD : (Fintype.card P.Errors : ℝ) = ((P.b : ℝ) + 1) ^ (P.r / 2) := by
    simp [StarParams.Errors, Fintype.card_option]
  have hK : (0 : ℝ) < (P.b : ℝ) + 1 := by positivity
  have hDpos : (0 : ℝ) < Fintype.card P.Errors := by rw [hD]; positivity
  have hpaid : (H.card : ℝ) * (dstar : ℝ) ≤ W := by
    exact_mod_cast heavy_card_mul_le degree dstar W hW
  have hH : (H.card : ℝ) / ((P.b : ℝ) + 1) ≤
      (W : ℝ) / ((dstar : ℝ) * ((P.b : ℝ) + 1)) := by
    have hd' : (0 : ℝ) < dstar := by exact_mod_cast hd
    rw [div_le_div_iff₀ hK (mul_pos hd' hK)]
    nlinarith
  have hratio : ∀ (A : ℕ), A ≤ (P.b + 1) ^ (P.r / 2 - 1) * H.card →
      (A : ℝ) / (Fintype.card P.Errors : ℝ) ≤
        (W : ℝ) / ((dstar : ℝ) * ((P.b : ℝ) + 1)) := by
    intro A hA
    have hA' : (A : ℝ) ≤ ((P.b : ℝ) + 1) ^ (P.r / 2 - 1) * (H.card : ℝ) := by
      exact_mod_cast hA
    apply le_trans (div_le_div_of_nonneg_right hA' hDpos.le)
    calc
      _ = (H.card : ℝ) / ((P.b : ℝ) + 1) := by
        rw [hD, show P.r / 2 = (P.r / 2 - 1) + 1 by omega, pow_succ]
        field_simp
        simp only [Nat.add_sub_cancel]
        ring
      _ ≤ _ := hH
  have hL := hratio L (star_hit_card_le P P.leftBlock P.leftBlock_inj H)
  have hR := hratio R (star_hit_card_le P P.rightBlock P.rightBlock_inj H)
  rw [structural_bad_pair_card]
  change ((L * R : ℕ) : ℝ) / (Fintype.card P.Errors : ℝ) ^ 2 ≤ _
  push_cast
  calc
    _ = ((L : ℝ) / (Fintype.card P.Errors : ℝ)) *
        ((R : ℝ) / (Fintype.card P.Errors : ℝ)) := by
      rw [div_mul_div_comm, sq]
    _ ≤ ((W : ℝ) / ((dstar : ℝ) * ((P.b : ℝ) + 1))) *
        ((W : ℝ) / ((dstar : ℝ) * ((P.b : ℝ) + 1))) :=
      mul_le_mul hL hR (div_nonneg (Nat.cast_nonneg _) hDpos.le) (by positivity)
    _ = _ := (sq _).symm

end NearQuarticWires.Mask
