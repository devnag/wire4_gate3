import Proof.Quartic.StageGamma.PairAccumulator

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open scoped BigOperators

/-- `cor:conditional`, paper/paper.tex: every
actual partial natural pair has exactly the sum of its ORIGINAL signed
term values, without any assumption on their signs. -/
theorem originalPartialPair_value (request : Machine.GammaRequest) (k : ℕ) :
    (originalPartialPair request k).value =
      ∑ i ∈ Finset.range k, (indexedTermPair request i).value := by
  simp [originalPartialPair, CoefficientPair.value, Nat.cast_sum, Finset.sum_sub_distrib]

/-- `cor:conditional`, paper/paper.tex: the exact
unfiltered base-Q+1 address census enumerates every ORIGINAL signed term
once and yields precisely the required scaled conditional coefficient. -/
theorem originalPartialPair_full_value (request : Machine.GammaRequest) :
    (originalPartialPair request ((request.parameters.Q + 1) ^ 8)).value =
      Machine.gammaTarget request := by
  rw [originalPartialPair_value, Finset.sum_range]
  have hi : ∀ i : Fin ((request.parameters.Q + 1) ^ 8),
      (indexedTermPair request i.val).value =
        (originalTermPair request (littleChoiceEquiv request.parameters.Q i)).value := by
    intro i
    simp only [indexedTermPair, dif_pos i.isLt]
  simp_rw [hi, originalTermPair_value]
  rw [← Finset.mul_sum]
  have he := (littleChoiceEquiv request.parameters.Q).sum_comp
    (fun choice => expansionTerm request choice)
  rw [he]
  exact (Cycle.scaledGamma_gauss request.parameters request.prefixLength request.prefixCode
    request.prefixFits request.walk).symm

end NearQuarticWires.StageGamma
