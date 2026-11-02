import Proof.Quartic.StageGamma.Kernel
import Proof.Quartic.StageGamma.Radix

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open scoped BigOperators
open NearCubicWires.WireExponent3_5

/-- `cor:conditional`, paper/paper.tex: the integer
contribution of one exact expansion choice before the common prefix scale. -/
noncomputable def expansionTerm (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : ℤ :=
  Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice *
    ((JoinElimination.condProbGauss request.parameters.modulus request.parameters.ell 8
      (2 * request.parameters.kh) request.prefixLength request.prefixCode
      (conjunction request choice)).1 : ℤ)

/-- `cor:conditional`, paper/paper.tex: every one-slot
integer coefficient fits in the field degree's binary width. -/
theorem choiceCoefficient_abs_le (request : Machine.GammaRequest)
    (a : Fin (request.parameters.Q + 1)) :
    (Cycle.choiceCoefficient request.parameters.N request.parameters.Q a).natAbs ≤
      2 ^ request.parameters.ell := by
  refine Fin.cases ?_ (fun j => ?_) a
  · simpa [Cycle.choiceCoefficient] using request.parameters.Q_le
  · simp only [Cycle.choiceCoefficient, Fin.cases_succ, Int.natAbs_neg, Int.natAbs_pow,
      Int.natAbs_natCast]
    change (2 ^ request.parameters.kh) ^ 2 ≤ _
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by have := request.parameters.k_le; omega)

/-- `cor:conditional`, paper/paper.tex: the product of
the eight coefficients has at most one seed length of magnitude bits. -/
theorem gammaChoiceWeight_abs_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (Cycle.gammaChoiceWeight request.parameters.N request.parameters.Q choice).natAbs ≤
      2 ^ Cycle.seedLength request.parameters := by
  have h : ∀ T : Finset (Fin 8),
      (∏ i ∈ T, Cycle.choiceCoefficient request.parameters.N request.parameters.Q (choice i)).natAbs ≤
        (2 ^ request.parameters.ell) ^ T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      simp only [Finset.prod_insert hi, Int.natAbs_mul, Finset.card_insert_of_notMem hi, pow_succ]
      calc
        _ ≤ (2 ^ request.parameters.ell) * (2 ^ request.parameters.ell) ^ T.card :=
          Nat.mul_le_mul (choiceCoefficient_abs_le request (choice i)) ih
        _ = _ := by ring
  simpa [Cycle.gammaChoiceWeight, Cycle.seedLength, ← pow_mul, Nat.mul_comm] using h Finset.univ

/-- `cor:conditional`, paper/paper.tex: a Gaussian
numerator counts a subset of the actual original seed completions. -/
theorem gaussianCount_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (JoinElimination.condProbGauss request.parameters.modulus request.parameters.ell 8
      (2 * request.parameters.kh) request.prefixLength request.prefixCode
      (conjunction request choice)).1 ≤ 2 ^ Cycle.seedLength request.parameters := by
  classical
  unfold conjunction
  rw [← Cycle.gammaChoice_gauss_count request.parameters request.prefixLength request.prefixCode
    request.prefixFits request.walk choice]
  calc
    _ ≤ (Finset.range (2 ^ (Cycle.seedLength request.parameters - request.prefixLength))).card :=
      Finset.card_filter_le _ _
    _ = 2 ^ (Cycle.seedLength request.parameters - request.prefixLength) := Finset.card_range _
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

/-- `cor:conditional`, paper/paper.tex: each actual
signed summand fits in twice the seed length of magnitude bits. -/
theorem expansionTerm_abs_le (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    (expansionTerm request choice).natAbs ≤ 2 ^ (2 * Cycle.seedLength request.parameters) := by
  dsimp [expansionTerm]
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  calc
    _ ≤ 2 ^ Cycle.seedLength request.parameters * 2 ^ Cycle.seedLength request.parameters :=
      Nat.mul_le_mul (gammaChoiceWeight_abs_le request choice) (gaussianCount_le request choice)
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- `prop:time`, paper/paper.tex: the exact radix census
fits in one seed length plus eight bits, including the case `Q=0`. -/
theorem choiceCount_le (request : Machine.GammaRequest) :
    (request.parameters.Q + 1) ^ 8 ≤ 2 ^ (Cycle.seedLength request.parameters + 8) := by
  have hq : request.parameters.Q + 1 ≤ 2 ^ (request.parameters.ell + 1) := by
    rw [pow_succ]
    have hp := request.parameters.Q_le
    have hpos : 1 ≤ 2 ^ request.parameters.ell := Nat.one_le_pow _ _ (by decide)
    omega
  calc
    _ ≤ (2 ^ (request.parameters.ell + 1)) ^ 8 := Nat.pow_le_pow_left hq 8
    _ = _ := by rw [← pow_mul]; congr 1; dsimp [Cycle.seedLength]; omega

/-- `cor:conditional`, paper/paper.tex: any already
visited subset of exact choices has a uniformly bounded signed accumulator. -/
theorem expansionPartial_abs_le (request : Machine.GammaRequest)
    (T : Finset (Cycle.GammaChoice request.parameters.Q)) :
    (∑ choice ∈ T, expansionTerm request choice).natAbs ≤
      2 ^ (3 * Cycle.seedLength request.parameters + 8) := by
  have hcard : T.card ≤ (request.parameters.Q + 1) ^ 8 := by
    simpa [Cycle.GammaChoice] using T.card_le_univ
  calc
    _ ≤ ∑ choice ∈ T, (expansionTerm request choice).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _choice ∈ T, 2 ^ (2 * Cycle.seedLength request.parameters) :=
      Finset.sum_le_sum (fun choice _ => expansionTerm_abs_le request choice)
    _ = T.card * 2 ^ (2 * Cycle.seedLength request.parameters) := by simp
    _ ≤ 2 ^ (Cycle.seedLength request.parameters + 8) *
        2 ^ (2 * Cycle.seedLength request.parameters) :=
      Nat.mul_le_mul_right _ (hcard.trans (choiceCount_le request))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the actual signed accumulator has a linear binary width,
including the prefix scale, for every partial exact enumeration. -/
theorem scaledPartial_fits (request : Machine.GammaRequest)
    (T : Finset (Cycle.GammaChoice request.parameters.Q)) :
    ((2 : ℤ) ^ request.prefixLength * ∑ choice ∈ T, expansionTerm request choice).natAbs <
      2 ^ (4 * Cycle.seedLength request.parameters + 9) := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  have hs : (2 : ℤ).natAbs ^ request.prefixLength ≤ 2 ^ Cycle.seedLength request.parameters :=
    Nat.pow_le_pow_right (by decide) request.prefixFits
  calc
    _ ≤ 2 ^ Cycle.seedLength request.parameters *
        2 ^ (3 * Cycle.seedLength request.parameters + 8) :=
      Nat.mul_le_mul hs (expansionPartial_abs_le request T)
    _ = 2 ^ (4 * Cycle.seedLength request.parameters + 8) := by rw [← pow_add]; congr 1; omega
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

end NearQuarticWires.StageGamma
