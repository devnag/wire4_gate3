import Proof.Quartic.StagePrintTuple.CallRecords

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print` and `prop:time`, paper/paper.tex: a genuine cold callee is reached only after its actual
finite input, blank work tapes, zero heads and reusable scratch have
been physically established in the controller state. -/
structure CallReady (p : Program) (s : Site p ns nr) (word : List Bool)
    (σ : WState ns nr) : Prop where
  input : ∀j,σ.st (s.bank j)=p.inputTapes word j
  heads : ∀j,σ.sh (s.bank j)=0
  tally : σ.st s.tally=[]
  tallyHead : σ.sh s.tally=0
  guard : σ.st s.guard=[]
  guardHead : σ.sh s.guard=0
  ruler : Worker.Blank (σ.st s.ruler)
  rulerHead : σ.sh s.ruler=0
  registers : ∀i,σ.val (s.regs i)=0

/-- `lem:print`, paper/paper.tex: appending a
genuine Cartesian or Stack raw-record reply and cleaning its call bank
has an exterior state independent of every callee work tape and clock. -/
theorem recordsCall_ready {Request : Type} {input : Request→List Bool}
    {records : Request→List (List Bool)} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>(records r).flatMap frame) budget) (req : Request)
    (hne : ∀ record∈records req,record≠[]) (cap : ℕ)
    (s : Site f.program ns nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hdB : ∀j,s.bank j≠dst) (hdT : dst≠s.tally) (hdG : dst≠s.guard) (hdL : dst≠s.ruler)
    (hOS : OP≠s.regs 0) (σ : WState ns nr) (ready : CallReady f.program s (input req) σ)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : 2*(input req).length+2+budget req≤cap)
    (hcapOut : σ.val OP+((records req).flatMap frame).length+1≤cap) :
    ∃τ,WXExec cap (callRecordsProgram s dst OP) σ τ (callRecordsCost (input req).length (budget req)) ∧
      SimW (appendO (cleanState s σ) dst OP ((records req).flatMap frame)) τ := by
  obtain ⟨tapes,steps,τ,_hs,he,hτ⟩ := callRecords_exec f req hne cap s dst OP
    hdB hdT hdG hOS σ ready.input ready.heads ready.tally ready.tallyHead
    ready.guard ready.guardHead ready.ruler ready.rulerHead ready.registers hdL hd hcap hcapOut
  refine ⟨τ,he,?_⟩
  simpa only [StagePrint.callAppendPost_eq s σ tapes (input req).length steps dst OP _ hdB hdT hdG] using hτ

/-- `lem:print`, paper/paper.tex: a genuine
finite framed reply is copied and its complete work bank cleaned
before the retained support, coefficient or native-pool cursor is used. -/
theorem framedCall_ready {Request : Type} {input cache : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (req : Request) (cap : ℕ)
    (s : Site f.program ns nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hdB : ∀j,s.bank j≠dst) (hdT : dst≠s.tally) (hdG : dst≠s.guard) (hdL : dst≠s.ruler)
    (hOS : OP≠s.regs 0) (σ : WState ns nr) (ready : CallReady f.program s (input req) σ)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : 2*(input req).length+2+budget req≤cap)
    (hcapOut : σ.val OP+(frame (cache req)).length+1≤cap) :
    ∃τ,WXExec cap (StagePrint.callAppendProgram s dst OP) σ τ
      (StagePrint.callAppendCost (input req).length (budget req)) ∧
      SimW (appendO (cleanState s σ) dst OP (frame (cache req))) τ := by
  obtain ⟨tapes,steps,τ,_hs,he,hτ⟩ := StagePrint.callAppend_exec f req cap s dst OP
    hdB hdT hdG hOS σ ready.input ready.heads ready.tally ready.tallyHead
    ready.guard ready.guardHead ready.ruler ready.rulerHead ready.registers hdL hd hcap hcapOut
  refine ⟨τ,he,?_⟩
  simpa only [StagePrint.callAppendPost_eq s σ tapes (input req).length steps dst OP _ hdB hdT hdG] using hτ

end NearQuarticWires.StageTuple
