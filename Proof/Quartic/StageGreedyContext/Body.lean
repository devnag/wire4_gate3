import Proof.Quartic.StageGreedyContext.Prepare

/-!
# One actual context computation followed by the unchanged carrier stream

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyContext

attribute [local irreducible] setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.Codec

/-- `lem:print`, paper/paper.tex: the
actual once-computed context is appended to the measured marked
arity word, and one delimiter seals their single combined frame. -/
def appendContext (p : Program) : WM (p.tapeCount+3) 24 :=
  .seq (.whs (bank p p.outputTape) (copyPairW (bank p p.outputTape) 1 (registers 13)))
    (emitC 1 (registers 13) false)

/-- `lem:print`, paper/paper.tex: the
fixed physical frontend prepares the literal input, invokes the actual
closed context machine once, and copies the unchanged suffix once. -/
noncomputable def contextBody (B1 B2 : ℕ) : WMX ((setup B1 B2).program.tapeCount+3) 24 :=
  let p:=(setup B1 B2).program
  .seq (.wm (prepareContext p))
    (.seq (.machZ p.machine (bank p) (ruler p))
      (.seq (.wm (appendContext p)) (.wm (finishContext 0 1 2 (registers 13) 20 21))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the whole actual frontend starts
with the literal framed carrier, computes its one common context and
prints the exact nested-context output with a linear suffix clock. -/
theorem contextBody_run {B1 B2 : ℕ} (r : Request B1 B2) :
    ∃last,WXExec r.capacity (contextBody B1 B2) r.start last r.sourceSteps ∧
      last.st 2=r.output := by
  let f:=setup B1 B2
  let p:=f.program
  let payload:=StagePrint.Context.word r.prepared
  let CP:=registers 13
  obtain ⟨a,ea,ha⟩:=prepareContext_spec r
  obtain ⟨b,eb,hout,hheads,hoff,hvals⟩:=wfDock_exact f r r.capacity (bank p) (bank_injective p)
    (ruler p) (bank_ne_ruler p) a ha.input ha.blank ha.heads r.setupBudget
    ha.rulerWord ha.rulerHead le_rfl
  have hbank0:= (bank_off p p.outputTape).1
  have hbank1:= (bank_off p p.outputTape).2.1
  have hbank2:= (bank_off p p.outputTape).2.2
  have bSource:=hoff 0 (fun j=>(bank_off p j).1)
  have bContext:=hoff 1 (fun j=>(bank_off p j).2.1)
  have bOutput:=hoff 2 (fun j=>(bank_off p j).2.2)
  have bCtxWord : b.st 1=Streaming.marks (natWord r.prepared.call.n):=
    bContext.1.trans ha.contextPrefix
  have bCtxHead : b.sh 1=2*(natWord r.prepared.call.n).length:=bContext.2.trans ha.contextHead
  have bCP : b.val CP=2*(natWord r.prepared.call.n).length:=by rw [hvals];exact ha.contextCount
  have hcontextLength : r.context.length=(natWord r.prepared.call.n).length+payload.length:=by
    simp only [Request.context,List.length_append,payload]
  have hlinear:=r.finish_capacity
  rw [hcontextLength] at hlinear
  have ec:=copyFrame_loop r.capacity (bank p p.outputTape) 1 hbank1 CP [] payload [] b
    (by simpa only [List.nil_append,List.append_nil] using hout) (hheads _)
    (by rw [bCtxWord,bCtxHead,Streaming.marks_length])
    (by rw [bCP];omega)
  simp only [List.length_nil,Nat.zero_add] at ec
  let c:=(appendO b 1 CP (Streaming.marks payload)).seth (bank p p.outputTape) (2*payload.length)
  have cCtxWord : c.st 1=Streaming.marks r.context := by
    simp only [c,WState.seth_st,appendO_st,Function.update_self,bCtxWord,
      Request.context,Streaming.marks_append,payload]
  have cCtxHead : c.sh 1=2*r.context.length := by
    simp only [c,WState.seth_sh,Function.update_of_ne hbank1.symm,appendO_sh,
      Function.update_self,bCtxHead,Streaming.marks_length,hcontextLength]
    omega
  have cCP : c.val CP=2*r.context.length := by
    simp only [c,WState.seth_val,appendO_val,Function.update_self,bCP,
      Streaming.marks_length,hcontextLength]
    omega
  have ed:=emitC_spec r.capacity (1 : Fin (p.tapeCount+4)) CP false c
    (by rw [cCtxWord,cCtxHead,Streaming.marks_length]) (by rw [cCP];omega)
  let d:=appendO c 1 CP [false]
  have dCtxWord : d.st 1=frame r.context := by
    simp only [d,appendO_st,Function.update_self,cCtxWord,frame_eq_marks]
  have hlen : (frame r.context).length=2*r.context.length+1 := by
    rw [frame_eq_marks]
    simp only [List.length_append,Streaming.marks_length,List.length_singleton]
  have dCtxHead : d.sh 1=(frame r.context).length := by
    simp only [d,appendO_sh,Function.update_self,cCtxHead,List.length_singleton,hlen]
  have dCP : d.val CP=(frame r.context).length := by
    simp only [d,appendO_val,Function.update_self,cCP,List.length_singleton,hlen]
  have h10 : (1 : Fin (p.tapeCount+4))≠0 := by
    intro h;have hh:=congrArg Fin.val h
    change 1%(p.tapeCount+4)=0 at hh
    rw [Nat.mod_eq_of_lt (by omega)] at hh;omega
  have h21 : (2 : Fin (p.tapeCount+4))≠1 := by
    intro h;have hh:=congrArg Fin.val h
    change 2%(p.tapeCount+4)=1%(p.tapeCount+4) at hh
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at hh;omega
  have dSource : d.st 0=frame r.word := by
    simp only [d,appendO_st,Function.update_of_ne h10.symm,c,WState.seth_st,
      bSource.1,ha.source]
  have dSourceHead : d.sh 0=2*(natWord r.prep.length++r.prep).length := by
    simp only [d,appendO_sh,Function.update_of_ne h10.symm,c,WState.seth_sh,
      Function.update_of_ne hbank0.symm,bSource.2,ha.position]
  have dOut : d.st 2=[] := by
    simp only [d,appendO_st,Function.update_of_ne h21,c,WState.seth_st,bOutput.1,ha.output]
  have dOutHead : d.sh 2=0 := by
    simp only [d,appendO_sh,Function.update_of_ne h21,c,WState.seth_sh,
      Function.update_of_ne hbank2.symm,bOutput.2,ha.outputHead]
  have d20 : d.val (20 : Fin 24)=0 := by
    simp [d,c,appendO,CP,registers,hvals,ha.outputCount]
  have d21 : d.val (21 : Fin 24)=0 := by
    simp [d,c,appendO,CP,registers,hvals,ha.scanCount]
  have h02 : (0 : Fin (p.tapeCount+4))≠2 := by
    intro h
    have hh:=congrArg Fin.val h
    change 0=2%(p.tapeCount+4) at hh
    rw [Nat.mod_eq_of_lt (by omega)] at hh
    omega
  obtain ⟨last,ef,hfinal⟩:=finishContext_spec r.capacity (0 : Fin (p.tapeCount+4)) 1 2
    CP 20 21 h10.symm h02 h21.symm
    (by decide) r.context r.suffix (Streaming.marks (natWord r.prep.length++r.prep)) d
    (by rw [dSource];simp only [Request.word,frame_eq_marks,Streaming.marks_append,List.append_assoc])
    (by rw [dSourceHead,Streaming.marks_length]) dCtxWord dCtxHead dOut dOutHead dCP d20 d21
    r.finish_capacity
  refine ⟨last,?_,hfinal⟩
  have eappend : WExec r.capacity (appendContext p) b d (22*payload.length+9) := by
    exact (ec.seq ed).mono (by omega)
  have ecall : WXExec r.capacity (.machZ p.machine (bank p) (ruler p)) a b
      (2*r.setupBudget+2) := eb
  change WExec r.capacity (prepareContext p) r.start a r.prefixSteps at ea
  have hall:= (WXExec.wm ea).seq (ecall.seq ((WXExec.wm eappend).seq (WXExec.wm ef)))
  change WXExec r.capacity
    (.seq (.wm (prepareContext p)) (.seq (.machZ p.machine (bank p) (ruler p))
      (.seq (.wm (appendContext p)) (.wm (finishContext 0 1 2 CP 20 21)))))
    r.start last r.sourceSteps
  exact hall.mono (by
    unfold Request.sourceSteps
    change _≤r.prefixSteps+2*r.setupBudget+30*payload.length+
      finishContextCost r.context r.suffix+100
    omega)

end NearQuarticWires.StageGreedyContext
