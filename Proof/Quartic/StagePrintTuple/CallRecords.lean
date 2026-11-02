import Proof.Quartic.StagePrintTuple.RecordsCopy
import Proof.Quartic.StagePrint.CallStates

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one reusable call appends a raw nonempty fixed-field record stream before erasing its work bank. -/
noncomputable def callRecordsProgram {p : Program} (s : Site p ns nr) (dst : Fin (ns+1)) (OP : Fin nr) : WMX ns nr :=
  .seq (callP s) (.seq (.wm (appendRecordsReset (s.bank p.outputTape) dst OP (s.regs 0))) (cleanP s))

/-- `prop:time`, paper/paper.tex: a complete call, actual raw-record copy, and bank cleanup have one linear source clock. -/
def callRecordsCost (inputLength budget : ℕ) : ℕ := 400*(inputLength+budget+1)

/-- `lem:print`, paper/paper.tex: an actual nonempty-record-output computation can be reused on a fixed bank without observing a callee output length or supplying a fixed record count. -/
theorem callRecords_exec {Request : Type} {input : Request→List Bool} {records : Request→List (List Bool)} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>(records r).flatMap frame) budget) (req : Request)
    (hne : ∀ record∈records req,record≠[]) (cap : ℕ)
    (s : Site f.program ns nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (hdB : ∀j,s.bank j≠dst) (hdT : dst≠s.tally) (hdG : dst≠s.guard)
    (hOS : OP≠s.regs 0) (σ : WState ns nr)
    (hin : ∀j,σ.st (s.bank j)=f.program.inputTapes (input req) j)
    (h0 : ∀j,σ.sh (s.bank j)=0) (hTL : σ.st s.tally=[]) (hTLh : σ.sh s.tally=0)
    (hG : σ.st s.guard=[]) (hGh : σ.sh s.guard=0)
    (hL : Worker.Blank (σ.st s.ruler)) (hLh : σ.sh s.ruler=0)
    (hR : ∀i,σ.val (s.regs i)=0)
    (hdL : dst≠s.ruler) (hd : σ.sh dst=(σ.st dst).length)
    (hcap : 2*(input req).length+2+budget req≤cap)
    (hcapOut : σ.val OP+((records req).flatMap frame).length+1≤cap) :
    ∃ (tapes : Fin f.program.tapeCount→List Bool) (steps : ℕ) (τ : WState ns nr),
      steps≤budget req ∧
      WXExec cap (callRecordsProgram s dst OP) σ τ (callRecordsCost (input req).length (budget req)) ∧
      SimW (cleanState s (appendO (calledState s σ tapes (input req).length steps)
        dst OP ((records req).flatMap frame))) τ := by
  obtain ⟨tapes,steps,τ,ht,hsteps,hlen,hfar,ec,hs⟩:=
    callP_exec f req cap s σ hin h0 hTL hTLh hG hGh hL hLh hR hcap
  let cs:=calledState s σ tapes (input req).length steps
  have csBank (j) : cs.st (s.bank j)=tapes j := by
    simp only [cs,calledState,WState.sets_st,Function.update_of_ne (s.guard_ne j),
      Function.update_of_ne (s.tally_ne j)]
    exact updS_st_slot s.bank σ (fun _=>0) tapes s.bank_inj j
  have csHead (j) : cs.sh (s.bank j)=0 :=
    updS_sh_slot s.bank σ (fun _=>0) tapes s.bank_inj j
  have csOther (i : Fin (ns+1)) (hb : ∀j,s.bank j≠i) (hT : i≠s.tally) (hG : i≠s.guard) :
      cs.st i=σ.st i ∧ cs.sh i=σ.sh i := by
    constructor
    · simp only [cs,calledState,WState.sets_st,Function.update_of_ne hG,Function.update_of_ne hT]
      exact updS_st_other s.bank σ (fun _=>0) tapes i hb
    · exact updS_sh_other s.bank σ (fun _=>0) tapes i hb
  have cp:=appendRecordsReset_spec cap (s.bank f.program.outputTape) dst OP (s.regs 0)
    (hdB _) hOS (records req) [] hne (by rfl) cs (by rw [csBank,ht];simp) (csHead _)
    (by rw [(csOther dst hdB hdT hdG).1,(csOther dst hdB hdT hdG).2];exact hd)
    (hR 0) hcapOut
  let copied:=appendO cs dst OP ((records req).flatMap frame)
  have copiedBank (j) : copied.st (s.bank j)=tapes j := by
    simp only [copied,appendO,WState.setv_st,WState.seth_st,WState.sets_st,
      Function.update_of_ne (hdB j)]
    exact csBank j
  have copiedHead (j) : copied.sh (s.bank j)=0 := by
    simp only [copied,appendO,WState.setv_sh,WState.seth_sh,WState.sets_sh,
      Function.update_of_ne (hdB j)]
    exact csHead j
  have cst : copied.st s.tally=List.replicate steps true := by
    simp [copied,appendO,hdT.symm,cs,calledState,Function.update_of_ne s.tally_guard]
  have csth : copied.sh s.tally=0 := by
    simp [copied,appendO,hdT.symm,cs,calledState,
      updS_sh_other _ _ _ _ _ s.tally_ne,hTLh]
  have csg : copied.st s.guard=List.replicate (guardLength (input req).length steps) true := by
    simp [copied,appendO,hdG.symm,cs,calledState]
  have csgh : copied.sh s.guard=0 := by
    simp [copied,appendO,hdG.symm,cs,calledState,
      updS_sh_other _ _ _ _ _ s.guard_ne,hGh]
  have csl : copied.st s.ruler=σ.st s.ruler := by
    simp only [copied,appendO,WState.setv_st,WState.seth_st,WState.sets_st,
      Function.update_of_ne hdL.symm]
    exact (csOther s.ruler s.ruler_ne s.tally_ruler.symm s.guard_ruler.symm).1
  have cslh : copied.sh s.ruler=0 := by
    simp only [copied,appendO,WState.setv_sh,WState.seth_sh,WState.sets_sh,
      Function.update_of_ne hdL.symm]
    rw [(csOther s.ruler s.ruler_ne s.tally_ruler.symm s.guard_ruler.symm).2,hLh]
  have csr : copied.val (s.regs 0)=0 := by
    simp [copied,appendO,hOS.symm,cs,calledState,updS,hR]
  obtain ⟨τclean,ee,hsc⟩:=cleanP_exec cap s (guardLength (input req).length steps) copied
    (by intro j q hq;rw [copiedBank];exact hfar j q hq) copiedHead
    (by intro q hq;rw [cst];exact readTapeBit_beyond _ _ (by simp;unfold guardLength at hq;omega))
    csth csg csgh (by rw [csl];exact hL) cslh csr (by unfold guardLength;omega)
  obtain ⟨τcopy,ecp,hcp⟩:=wxexec_sim (WXExec.wm cp) τ hs
  obtain ⟨τfinal,eef,hsf⟩:=wxexec_sim ee τcopy hcp
  refine ⟨tapes,steps,τfinal,hsteps,?_,SimW.trans hsc hsf⟩
  refine (WXExec.seq ec (WXExec.seq ecp eef)).mono ?_
  unfold callRecordsCost callCost appendRecordsCost cleanCost guardLength
  rw [ht] at hlen
  omega

end NearQuarticWires.StageTuple
