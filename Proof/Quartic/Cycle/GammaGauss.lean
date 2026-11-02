import Proof.Quartic.Cycle.GammaExpansion

set_option autoImplicit false

namespace NearQuarticWires.Cycle
attribute [local instance] Classical.propDecidable
open Finset
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.GF2

/-- Paper `cor:conditional`: at most eight affine field constraints,
with actual labels below Q, without padding them to the field size. -/
noncomputable def gammaChoiceCons (P : SeedParameters) (w : Walk P.N 4)
    (α : GammaChoice P.Q) : List (ℕ × ℕ) :=
  (List.finRange 8).filterMap fun l =>
    (sampleChoice (α l)).map fun j => ((j : ℕ), cellNum P (edge (by norm_num) w l))

/-- Paper `cor:conditional`: each event contains at most eight equations. -/
theorem gammaChoiceCons_length (P : SeedParameters) (w : Walk P.N 4)
    (α : GammaChoice P.Q) : (gammaChoiceCons P w α).length ≤ 8 := by
  unfold gammaChoiceCons
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- Paper `cor:conditional`: the actual seed equations are precisely
those selected by the (Q+1)^8 expansion. -/
theorem gammaChoiceCons_ok (P : SeedParameters) (plen pre : ℕ)
    (w : Walk P.N 4) (α : GammaChoice P.Q) (r : ℕ) :
    consOk P.modulus P.ell 8 (2*P.kh) plen pre (gammaChoiceCons P w α) r = true ↔
      ∀ l, choiceMatches (seedSample P (completion plen pre r))
        (edge (by norm_num) w l) (α l) := by
  classical
  unfold consOk gammaChoiceCons
  rw [List.all_eq_true]
  constructor
  · intro h l
    unfold choiceMatches
    cases ha : sampleChoice (α l) with
    | none => trivial
    | some j =>
      have hc := h ((j : ℕ), cellNum P (edge (by norm_num) w l)) (by
        rw [List.mem_filterMap]
        exact ⟨l, List.mem_finRange l, by simp [ha]⟩)
      exact (pos_eq_iff P _ j _).mpr (by simpa [completion] using hc)
  · intro h x hx
    rw [List.mem_filterMap] at hx
    obtain ⟨l, _, hl⟩ := hx
    cases ha : sampleChoice (α l) with
    | none => simp [ha] at hl
    | some j =>
      simp [ha] at hl
      subst hl
      have hc : seedSample P (completion plen pre r) j = edge (by norm_num) w l := by
        simpa only [choiceMatches, ha] using h l
      have he := (pos_eq_iff P _ j _).mp hc
      simpa [completion] using he

/-- Paper `cor:conditional`: the Gaussian system has valid field labels
and projected cell words. The primitive modulus is cached setup data `P.modulus`. -/
theorem gammaChoiceCons_bounds (P : SeedParameters) (w : Walk P.N 4)
    (α : GammaChoice P.Q) :
    ∀ x ∈ gammaChoiceCons P w α, x.1 < 2^P.ell ∧ x.2 < 2^(2*P.kh) := by
  intro x hx
  unfold gammaChoiceCons at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨l, _, hl⟩ := hx
  cases ha : sampleChoice (α l) with
  | none => simp [ha] at hl
  | some j =>
    simp [ha] at hl
    subst hl
    exact ⟨lt_of_lt_of_le j.isLt P.Q_le, ofVec_lt _⟩

/-- Paper `cor:conditional`: exact conditional event count by Gaussian
elimination, using one precomputed primitive modulus, not a primitive search per term. -/
theorem gammaChoice_gauss_count (P : SeedParameters) (plen pre : ℕ)
    (hplen : plen ≤ seedLength P) (w : Walk P.N 4) (α : GammaChoice P.Q) :
    ((Finset.range (2^(seedLength P-plen))).filter fun r =>
      ∀ l, choiceMatches (seedSample P (completion plen pre r))
        (edge (by norm_num) w l) (α l)).card =
    (JoinElimination.condProbGauss P.modulus P.ell 8 (2*P.kh) plen pre
      (gammaChoiceCons P w α)).1 := by
  classical
  rw [condProbGauss_eq_brute P.modulus P.ell 8 (2*P.kh) plen pre _
    P.cert.2.1 P.one_le_ell P.k_le hplen (gammaChoiceCons_bounds P w α), condProbBrute_fst]
  congr 1
  apply Finset.filter_congr
  intro r _
  exact (gammaChoiceCons_ok P plen pre w α r).symm

/-- Paper `cor:conditional`: the signed completion sum is computed by
EXACTLY (Q+1)^8 Gaussian counts, each on at most eight projected evaluations. -/
theorem gammaCompletionSum_gauss (P : SeedParameters) (plen pre : ℕ)
    (hplen : plen ≤ seedLength P) (w : Walk P.N 4) :
    gammaCompletionSum P plen pre w =
      ∑ α : GammaChoice P.Q, gammaChoiceWeight P.N P.Q α *
        ((JoinElimination.condProbGauss P.modulus P.ell 8 (2*P.kh) plen pre
          (gammaChoiceCons P w α)).1 : ℤ) := by
  classical
  unfold gammaCompletionSum
  simp_rw [walkGammaInt_choice_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.mul_sum, ← gammaChoice_gauss_count P plen pre hplen w α,
    Finset.natCast_card_filter]

/-- Paper `cor:conditional`: exact Gaussian formula for the concrete
signed integer requested by the machine; no padded label census is hidden. -/
theorem scaledGamma_gauss (P : SeedParameters) (plen pre : ℕ)
    (hplen : plen ≤ seedLength P) (w : Walk P.N 4) :
    scaledGamma P plen pre w = (2 : ℤ)^plen *
      ∑ α : GammaChoice P.Q, gammaChoiceWeight P.N P.Q α *
        ((JoinElimination.condProbGauss P.modulus P.ell 8 (2*P.kh) plen pre
          (gammaChoiceCons P w α)).1 : ℤ) := by
  unfold scaledGamma
  rw [gammaCompletionSum_gauss P plen pre hplen w]

#print axioms scaledGamma_gauss
end NearQuarticWires.Cycle
