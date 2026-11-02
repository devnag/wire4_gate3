import Proof.Quartic.StagePrintContext.Framing
import Proof.Quartic.StagePrint.HeaderSource
import Proof.Quartic.StageLift.FrameWrite
import Proof.Gates.Cells.Run

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageRecovery.OutputFrame
open StagePrint.Header

/-- `lem:print`, paper/paper.tex: the first
context field is the actual retained original call with its two frame layers. -/
def emitCallField : St VV MM := framedProgram (StageLift.emitMemoryFrame StageLift.callStore)

/-- `lem:print` and `prop:time`, paper/paper.tex: every original call bit and both marker layers are
physically emitted before any later header scratch can overwrite the
actual decoder's call-length register. -/
theorem emitCallField_run (C : Ctx) (r : HeaderCall) (a : DS VV MM)
    (hc : Cst a) (ha : Valid C a) (hd : HeaderSourceData r a)
    (hlen : a.env StageMain.CallSkip.lengthCounter=(callWord r.call).length)
    (hfit : (callWord r.call).length<2^C.Wd) (hW : 1≤C.Wd) :
    Hs C emitCallField a (40*((callWord r.call).length+1)) (fun b=>
      b.out=a.out++frame (frame (callWord r.call)) ∧b.ip=a.ip ∧b.ram=a.ram ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧Cst b ∧Valid C b) := by
  let clean : DS VV MM:={a with out:=[]}
  have hcursor : a.rc StageLift.callStore≤(callWord r.call).length := by
    have hh:=ha.rc_le StageLift.callStore
    simpa only [hd.originalCall,List.length_map] using hh
  have er:=StageLift.emitMemoryFrame_spec C StageLift.callStore (callWord r.call) clean
    ⟨hc.z,hc.one,hc.two⟩ hd.originalCall hlen hfit
  obtain ⟨b,n,he,hn,hout,hip,hram,_hrc,hstreams,hbc,_hfr⟩:=er
  change n≤a.rc StageLift.callStore+10*(callWord r.call).length+8 at hn
  have hframe:=StageLift.framedProgram_afterPrefix he rfl a.out
  have hstart : {clean with out:=a.out}=a := by cases a;rfl
  rw [hstart] at hframe
  let last : DS VV MM:={b with out:=a.out++frame b.out}
  have hvalid:=hframe.valid hW (callee_hB C) ha
  refine ⟨last,3*n+2,hframe,by omega,?_,hip,hram,hstreams,⟨hbc.z,hbc.one,hbc.two⟩,hvalid⟩
  simpa only [last,clean,List.nil_append] using congrArg (fun bits=>a.out++frame bits) hout

end NearQuarticWires.StagePrintContext
