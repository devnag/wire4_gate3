import Proof.Quartic.StageTupleTermPrice.Native
import Proof.Quartic.StageTupleTermPrice.Elements

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open StageTuple StageNativeKids

/-- `prop:time`, paper/paper.tex: the
actual native count decoder's quadratic cost is additive to the
actual source/callee price and fits the unchanged child/tuple square. -/
theorem price_nativePhase : WeightedPrice Step.small Step.square
    (fun j=>nativePhaseMagnitude NativeKidsRequest.budget j.nativeRequest) := by
  have hw : Price Step.small (fun j=>j.nativeRequest.word.length):=⟨50,1,by simpa only [pow_one] using Step.native_word_bound⟩
  have hc : WeightedPrice Step.small Step.square
      (fun j=>((j.nativeRequest.toRowContext.nativeKids j.nativeRequest.atom).length+1)^2) := by
    refine ⟨1,0,fun j=>?_⟩
    simp only [pow_zero,one_mul]
    change (j.tupleRequest.children.length+1)^2≤j.square
    exact j.square_elements.2.2.2
  have hh:=((WeightedPrice.of_price Step.square_pos hw).add Step.small_pos
    (WeightedPrice.of_price Step.square_pos price_nativeBudget)).add Step.small_pos hc
  exact hh.add Step.small_pos (WeightedPrice.of_price Step.square_pos (Price.constant Step.small 1))

end NearQuarticWires.StageTupleTermPrice
