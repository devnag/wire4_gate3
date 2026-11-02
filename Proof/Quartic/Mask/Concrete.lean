import Proof.Quartic.Mask.Filter
import Proof.Quartic.Mask.StarMass
import Proof.Quartic.Cells.Indexed

set_option autoImplicit false

namespace NearQuarticWires.Mask

open scoped BigOperators unitInterval
open Finset NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-- Paper `lem:smaskpop`: the concrete mixed population
of all listed gate occurrences on a product-star cell satisfies the
structural cap. Repeated gates remain separately charged. -/
theorem star_structural_population_lt (P : StarParams)
    (gates : List (NormalizedThresholdGate P.n)) (dstar : ℕ) (hd : 0 < dstar)
    (c : BitInput P.n) (u v : P.Errors)
    (hmask : structuralMask (P.flipSet P.leftBlock) (P.flipSet P.rightBlock)
      (heavyCoordinates (Cells.incidence gates) dstar) u v = true) :
    Cells.population P gates c u v < (P.r / 2) * dstar := by
  apply structural_population_lt (Cells.incidence gates)
    (P.flipSet P.leftBlock) (P.flipSet P.rightBlock) dstar (P.r / 2)
    (Cells.population P gates c) hd (by have := P.two_le_r; omega)
    (Cells.flipSet_card_le P P.leftBlock) (Cells.flipSet_card_le P P.rightBlock)
    (fun a b => (Cells.population_le_incidence P gates c a b).trans (min_le_left _ _))
    (fun a b => (Cells.population_le_incidence P gates c a b).trans (min_le_right _ _)) u v
  exact hmask

/-- Paper `sec:masks`: the actual sampling rate `τ/(4U)` is a
probability under the stated finite parameter guards. -/
noncomputable def filterRate (τ U : ℕ) (hU : 0 < U) (hτU : τ ≤ U) : unitInterval :=
  ⟨(τ : ℝ) / (4 * (U : ℝ)), by
    have hU' : (0 : ℝ) < U := by exact_mod_cast hU
    have hτU' : (τ : ℝ) ≤ U := by exact_mod_cast hτU
    constructor
    · positivity
    · rw [div_le_iff₀ (by positivity)]
      linarith⟩

/-- Paper `lem:filter` (a): the printed guarantee
with the actual `τ/(4U)` sampling rate and population hypothesis. -/
theorem filter_small (N τ U : ℕ) (hU : 0 < U) (hτU : τ ≤ U) (hN : N ≤ U) :
    (filterLaw N (filterRate τ U hU hτU)).real {k | τ < k} ≤
      (Real.exp 1 / 4) ^ (τ + 1) := by
  apply filter_small_population
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hN' : (N : ℝ) ≤ U := by exact_mod_cast hN
  change (N : ℝ) * ((τ : ℝ) / (4 * (U : ℝ))) ≤ _
  calc
    _ ≤ (U : ℝ) * ((τ : ℝ) / (4 * (U : ℝ))) :=
      mul_le_mul_of_nonneg_right hN' (by positivity)
    _ = (τ : ℝ) / 4 := by field_simp

/-- Paper `lem:filter` (b): the printed guarantee
with the actual sampling rate and `population ≥ 16U`. -/
theorem filter_large (N τ U : ℕ) (hU : 0 < U) (hτU : τ ≤ U) (hN : 16 * U ≤ N) :
    (filterLaw N (filterRate τ U hU hτU)).real {k | k ≤ τ} ≤
      Real.exp (-9 * (τ : ℝ) / 8) := by
  apply filter_large_population
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hN' : 16 * (U : ℝ) ≤ N := by exact_mod_cast hN
  change 4 * (τ : ℝ) ≤ (N : ℝ) * ((τ : ℝ) / (4 * (U : ℝ)))
  calc
    _ = (16 * (U : ℝ)) * ((τ : ℝ) / (4 * (U : ℝ))) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hN' (by positivity)

/-- Paper `lem:filter` (c): the actual population and
integer-floor budget imply the mean bound required by the structural tail. -/
theorem structural_mean_le (N τ U Xmax halfBlocks dstar : ℕ)
    (hU : 0 < U) (hτU : τ ≤ U) (hN : N ≤ halfBlocks * dstar)
    (hbudget : 3 * (2 * halfBlocks) * τ * dstar ≤ 2 * Xmax * U) :
    (N : ℝ) * (filterRate τ U hU hτU : ℝ) ≤ (Xmax : ℝ) / 12 := by
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hN' : (N : ℝ) ≤ (halfBlocks : ℝ) * (dstar : ℝ) := by exact_mod_cast hN
  have hb : 3 * (2 * (halfBlocks : ℝ)) * (τ : ℝ) * (dstar : ℝ) ≤
      2 * (Xmax : ℝ) * (U : ℝ) := by exact_mod_cast hbudget
  have hNt := mul_le_mul_of_nonneg_right hN' (Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)
  change (N : ℝ) * ((τ : ℝ) / (4 * (U : ℝ))) ≤ _
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith

/-- Paper `lem:filter` (c): complete structural
filter bound with the actual rate, population, and integer digit cutoff budget. -/
theorem filter_structural (N τ U Xmax halfBlocks dstar : ℕ)
    (hU : 0 < U) (hτU : τ ≤ U) (hN : N ≤ halfBlocks * dstar)
    (hbudget : 3 * (2 * halfBlocks) * τ * dstar ≤ 2 * Xmax * U) :
    (filterLaw N (filterRate τ U hU hτU)).real
      {k | (Xmax : ℝ) / 2 ≤ (k : ℝ)} ≤ (2 : ℝ) ^ (-(Xmax : ℝ) / 2) :=
  filter_structural_population N Xmax _
    (structural_mean_le N τ U Xmax halfBlocks dstar hU hτU hN hbudget)

end NearQuarticWires.Mask
