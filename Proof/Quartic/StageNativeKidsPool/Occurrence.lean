import Proof.Quartic.StageNativeKids.CounterInput
import Proof.Quartic.StagePrintTuple.CallRecords

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control StagePrint StageTuple StageNativeKids

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a computed
original-child index formats a real row call, appends its raw signed
fields and advances once, retaining the original source and header. -/
noncomputable def occurrenceProgram {p : Program} (s : Site p ns nr)
    (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 5 ↪ Fin nr)
    (OUT : Fin (ns+1)) (OP : Fin nr) : WMX ns nr :=
  .seq (.wm (pipelineCounterInputProgram P R))
    (.seq (callRecordsProgram s OUT OP) (WMX.inc (R 0)))

/-- `prop:time`, paper/paper.tex: each
original-child occurrence includes all input formatting, raw field
copying, bank cleanup and index progression. -/
def occurrenceCost (source header : List Bool) (j inputLength budget : ℕ) : ℕ :=
  pipelineCounterInputCost source header j+callRecordsCost inputLength budget+10

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual raw-record row call restores its
reusable bank and preserves all exterior source and accumulated data. -/
theorem occurrence_exec {Request : Type} {input : Request→List Bool}
    {records : Request→List (List Bool)} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>(records r).flatMap frame) budget)
    (req : Request) (hne : ∀ record∈records req,record≠[]) (cap : ℕ)
    (s : Site f.program ns nr) (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 5 ↪ Fin nr)
    (OUT : Fin (ns+1)) (OP : Fin nr)
    (hPI : P 2=s.input)
    (hOB : ∀j,s.bank j≠OUT) (hOT : OUT≠s.tally) (hOG : OUT≠s.guard)
    (hOL : OUT≠s.ruler) (hOR : ∀i,OP≠R i) (hOS : OP≠s.regs 0)
    (σ : WState ns nr) (source header : List Bool) (j : ℕ)
    (hinput : input req=pipelineInputWord source (List.replicate j true) header)
    (hb : ∀k,σ.st (s.bank k)=[]) (hh : ∀k,σ.sh (s.bank k)=0)
    (hTL : σ.st s.tally=[]) (hTLh : σ.sh s.tally=0)
    (hG : σ.st s.guard=[]) (hGh : σ.sh s.guard=0)
    (hL : Worker.Blank (σ.st s.ruler)) (hLh : σ.sh s.ruler=0)
    (hS : ∀i,σ.val (s.regs i)=0) (hj : σ.val (R 0)=j)
    (hz : ∀i,i≠0→σ.val (R i)=0)
    (hsrc : σ.st (P 0)=frame source) (hhead : σ.st (P 1)=frame header)
    (hheads : ∀i,σ.sh (P i)=0) (hout : σ.sh OUT=(σ.st OUT).length)
    (hwrite : 4*((frame source).length+(frame header).length)+8*j+100≤cap)
    (hcall : 2*(input req).length+2+budget req≤cap)
    (hcopy : σ.val OP+((records req).flatMap frame).length+1≤cap) :
    ∃ τ,WXExec cap (occurrenceProgram s P R OUT OP) σ τ
      (occurrenceCost source header j (input req).length (budget req)) ∧
      SimW ((appendO σ OUT OP ((records req).flatMap frame)).setv (R 0) (j+1)) τ := by
  have ew:=pipelineCounterInputProgram_spec cap P R source header j σ hsrc hhead hheads
    (by rw [hPI];exact hb _) hj hz hwrite
  rw [←hinput,hPI] at ew
  let σ1:=σ.sets s.input (frame (input req))
  have h1in : ∀k,σ1.st (s.bank k)=f.program.inputTapes (input req) k := by
    intro k
    by_cases hk : k=WorkerArith.inTape f.program
    · subst hk
      simp [σ1,Site.input,Program.inputTapes,WorkerArith.inTape]
    · have hn : s.bank k≠s.input:=s.bank_inj.ne hk
      have hk0 : k.val≠0:=by
        intro h
        exact hk ((WorkerArith.inTape_iff f.program k).2 h)
      simp [σ1,hn,Program.inputTapes,hk0,hb]
  have h1T : σ1.st s.tally=[]:=by simp [σ1,Site.input,(s.tally_ne _).symm,hTL]
  have h1G : σ1.st s.guard=[]:=by simp [σ1,Site.input,(s.guard_ne _).symm,hG]
  have h1L : Worker.Blank (σ1.st s.ruler):=by
    simpa [σ1,Site.input,(s.ruler_ne _).symm] using hL
  have h1out : σ1.sh OUT=(σ1.st OUT).length:=by
    simpa [σ1,Site.input,(hOB _).symm] using hout
  obtain ⟨tapes,steps,τc,hsteps,ec,hs⟩:=callRecords_exec f req hne cap s OUT OP
    hOB hOT hOG hOS σ1 h1in hh h1T hTLh h1G hGh h1L hLh hS hOL h1out hcall hcopy
  have hclean : cleanState s σ1=σ := by
    change cleanState s (σ.sets (s.bank (WorkerArith.inTape f.program)) (frame (input req)))=σ
    rw [cleanState_set_bank,cleanState_self s σ hb hh hTL hG]
  rw [callAppendPost_eq s σ1 tapes (input req).length steps OUT OP
    ((records req).flatMap frame) hOB hOT hOG,hclean] at hs
  let ideal:=appendO σ OUT OP ((records req).flatMap frame)
  have hi : ideal.val (R 0)=j:=by simp [ideal,appendO,(hOR 0).symm,hj]
  have ei:=WXExec.inc cap (R 0) ideal (by rw [hi];omega)
  rw [hi] at ei
  obtain ⟨τ,ea,ha⟩:=wxexec_sim ei τc hs
  refine ⟨τ,(WXExec.seq (WXExec.wm ew) (WXExec.seq ec ea)).mono ?_,ha⟩
  unfold occurrenceCost
  omega

end NearQuarticWires.StageNativeKidsPool
