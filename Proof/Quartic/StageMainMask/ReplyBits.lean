import Proof.Quartic.StageMainMask.MaskReply

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
write the actual original predicate and computed numeric mask as two
literal raw payload bits before the final ordinary output framing. -/
def emitReplyBits : St VV MM :=
  .seq (emitB .emit predicateValue) (emitB .emit numericMaskValue)

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: both actual Boolean results are
written physically in the required predicate-then-mask order. -/
theorem emitReplyBits_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (pred mask : Bool) (hp : a.env predicateValue = pred.toNat)
    (hm : a.env numericMaskValue = mask.toNat) :
    Hs C emitReplyBits a 5 (fun b => b.out = a.out ++ [pred, mask]) := by
  unfold emitReplyBits
  refine Hs.seq (t1 := 2) (t2 := 2)
    (emitB_spec (snkO C) predicateValue (by decide) a hc trivial) ?_
  rintro b ⟨hbo, _hbrest, hbenv⟩
  have hbc : Cst b := ⟨(congrFun hbenv vZ).trans hc.z,
    (congrFun hbenv v1).trans hc.one, (congrFun hbenv v2).trans hc.two⟩
  have hbm : b.env numericMaskValue = mask.toNat := (congrFun hbenv _).trans hm
  refine (emitB_spec (snkO C) numericMaskValue (by decide) b hbc trivial).mono le_rfl ?_
  rintro d ⟨hdo, _hdrest, _hdenv⟩
  have hpred : decide (a.env predicateValue = 1) = pred := by rw [hp]; cases pred <;> rfl
  have hmask : decide (b.env numericMaskValue = 1) = mask := by rw [hbm]; cases mask <;> rfl
  change b.out = a.out ++ [decide (a.env predicateValue = 1)] at hbo
  change d.out = b.out ++ [decide (b.env numericMaskValue = 1)] at hdo
  rw [hdo, hbo, hpred, hmask, List.append_assoc]
  rfl

end NearQuarticWires.StageMainMask
