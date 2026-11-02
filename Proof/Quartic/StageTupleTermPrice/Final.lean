import Proof.Quartic.StageTupleTermPrice.Prepare
import Proof.Quartic.StageTupleTermPrice.Reverse
import Proof.Quartic.StageTupleFinishPrice.Final

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open StageTuple StageNativeKids

/-- `prop:time`, paper/paper.tex: the
four actual monomial stage clocks and three sequencing transitions
share one unchanged square census of that actual original support. -/
theorem price_termStage : WeightedPrice Case.small Case.weight
    (fun j=>termStageCost NativeKidsRequest.budget j.request j.index j.index_lt) := by
  have h1:=WeightedPrice.of_price Case.weight_pos (Price.constant Case.small 1)
  have ha:=WeightedPrice.of_price Case.weight_pos price_acquire
  have hp:=WeightedPrice.of_price Case.weight_pos price_prepare
  have hf : WeightedPrice Case.small Case.weight (fun j=>
      100000000*monomialFinishMagnitude j.request j.data j.term j.term_mem) := by
    obtain ⟨C,E,_hC,_hE,h⟩:=StageTupleFinishPrice.finishCostBound
    exact ⟨C,E,h⟩
  have hr:=(price_reverseLoop.add Case.small_pos h1).add Case.small_pos hf
  have hprep:=(hp.add Case.small_pos h1).add Case.small_pos hr
  exact (ha.add Case.small_pos h1).add Case.small_pos hprep

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete SAME actual monomial clock is priced
unconditionally using the fixed genuine NativeKids budget, actual
support cardinality and structural data excluding the Terms stream. -/
theorem termStageCostBound : TermStageCostBound := by
  obtain ⟨C,E,h⟩:=price_termStage
  refine ⟨C+1,E+1,by omega,by omega,fun r mc hm hk k hidx=>?_⟩
  let j : Case:=⟨r,mc,hm,hk,k,hidx⟩
  have hh:=h j
  have hs:=j.small_pos
  have he:=Nat.pow_le_pow_right hs (Nat.le_succ E)
  have hfinal:=hh.trans (Nat.mul_le_mul_right j.weight (Nat.mul_le_mul (Nat.le_succ C) he))
  exact hfinal

end NearQuarticWires.StageTupleTermPrice
