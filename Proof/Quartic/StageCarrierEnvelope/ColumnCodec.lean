import Proof.Quartic.StageCarrierEnvelope.Free

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `imp:partition` and `lem:print`, paper/paper.tex: binary shifts construct the original center
count from its small exponent, followed by its canonical binary codec.
No input field containing a column count is read or numerically decoded. -/
def emitColumnCount : St VV MM :=
  .seq (StageGamma.binaryPower powerIndex freeVar columnVar) (StageRecovery.emitVariable columnVar)

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact original column codec takes only linearly
many binary shifts and codec instructions in the original arity. -/
theorem emitColumnCount_run {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a)
    (hfree : a.env freeVar=r.child.call.n-r.child.selected.1.k)
    (hW : r.child.call.n+3≤C.Wd)
    (hcap : 4*(r.child.call.n+1)^2+r.child.call.n+20<2^C.Wd) :
    Hs C emitColumnCount a (100*(r.child.call.n+1)+100) (fun b=>
      b.out=a.out++natWord r.child.cellCall.ncol ∧ Cst b) := by
  let free:=r.child.call.n-r.child.selected.1.k
  have hn : free≤r.child.call.n := Nat.sub_le _ _
  have hbits : natBitLength r.child.cellCall.ncol≤2*free+1 := by
    have hh:=StageCertTests.power_bitLength_le 2 free
    rw [show natBitLength 2=2 from by decide] at hh
    simpa only [ncol_eq,free,Nat.mul_comm] using hh
  have ePower:=StageGamma.binaryPower_run C powerIndex freeVar columnVar
    (by decide) (by decide) (by decide) (by decide) a hc free hfree (by omega)
  unfold emitColumnCount
  refine (Hs.seq (t2:=40*natBitLength r.child.cellCall.ncol+42) ePower ?_).mono
    (by omega) (fun _ h=>h)
  rintro b ⟨hb,hs,hbc,_hf⟩
  have hv : b.env columnVar=r.child.cellCall.ncol := by rw [hb,ncol_eq]
  have ePrint:=StageRecovery.emitVariable_spec C b hbc columnVar (by decide) (by omega)
    (by rw [hv];nlinarith only [hbits,hn,hcap])
  rw [hv] at ePrint
  refine ePrint.mono le_rfl ?_
  rintro out ⟨ho,_hr,oc,_of⟩
  exact ⟨by rw [ho,hs.out],oc⟩

end NearQuarticWires.StageCarrierEnvelope
