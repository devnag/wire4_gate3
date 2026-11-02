import Proof.Quartic.StageNativeKidsTail.Acquire
import Proof.Quartic.StageNativeKidsTail.OutputBound

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab
open StageNativeKids StageResize

noncomputable def tailProgram (f : ResizeCallee) : WMX (f.program.tapeCount+3) 5 :=
  .seq (acquireProgram f)
    (.seq (.machZ f.program.machine (bank f.program.tapeCount) (ruler f.program.tapeCount))
      (.seq (.wm (appendMarkedRecordsReset (bank f.program.tapeCount f.program.outputTape)
        (out f.program.tapeCount) 0 1)) (.wm (emitC (out f.program.tapeCount) 0 false))))

noncomputable def tailSteps (r : ResizeTailRequest) : ℕ :=
  2*r.stream.budget+1000*(r.word.length+r.stream.output.length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal count prefix is retained outside a single
concrete resize call; every raw output field is physically copied and
the complete reply receives one real final outer-frame delimiter. -/
theorem tailProgram_run (f : ResizeCallee) (r : ResizeTailRequest) :
    ∃ final,WXExec (capacity r) (tailProgram f) (start f r) final (tailSteps r) ∧
      final.st (out f.program.tapeCount)=r.output := by
  obtain ⟨b,hcall,houtput,hheads,hoff,hregs⟩:=wfDock_exact f r.stream (capacity r)
    (bank f.program.tapeCount) (bank_injective _) (ruler f.program.tapeCount)
    (bank_ne_ruler _) (ready f r) (ready_input f r) (ready_bank_blank f r) (ready_bank_heads f r)
    r.stream.budget (ready_ruler f r).1 (ready_ruler f r).2 le_rfl
  have hbo:=hoff (out f.program.tapeCount) (fun j=>(bank_off _ j).2.2)
  have hbout : b.st (out f.program.tapeCount)=marks (countWord r) := hbo.1.trans (ready_out f r).1
  have hbhead : b.sh (out f.program.tapeCount)=2*(countWord r).length := hbo.2.trans (ready_out f r).2
  have hv0 : b.val 0=2*(countWord r).length := by rw [hregs,ready_values];rfl
  have hv1 : b.val 1=0 := by rw [hregs,ready_values];rfl
  have hc:=countWord_length_le r
  have ec:=appendMarkedRecordsReset_spec (capacity r)
    (bank f.program.tapeCount f.program.outputTape) (out f.program.tapeCount) 0 1
    (bank_off _ _).2.2 (by decide) (outputRecords r) [] (outputRecords_nonempty r) rfl b
    (by rw [houtput,output_shape,List.append_nil]) (hheads _)
    (by rw [hbout,hbhead];simp only [NearCubicWires.RepairOrdinary.Streaming.marks_length]) hv1
    (by rw [hv0,←output_shape];unfold capacity;omega)
  rw [←output_shape] at ec
  let c:=appendO b (out f.program.tapeCount) 0 (marks r.stream.output)
  have hchead:c.sh (out f.program.tapeCount)=(c.st (out f.program.tapeCount)).length := by
    simp only [c,appendO,WState.setv_sh,WState.seth_sh,Function.update_self,WState.setv_st,
      WState.seth_st,WState.sets_st,hbout,hbhead,List.length_append,
      NearCubicWires.RepairOrdinary.Streaming.marks_length]
  have hc0:c.val 0<capacity r := by
    simp only [c,appendO,WState.setv_val,Function.update_self,hv0,
      NearCubicWires.RepairOrdinary.Streaming.marks_length]
    unfold capacity;omega
  have ee:=emitC_spec (capacity r) (out f.program.tapeCount) (0 : Fin 5) false c hchead hc0
  refine ⟨appendO c (out f.program.tapeCount) 0 [false],?_,?_⟩
  · have whole:=(acquireProgram_run f r).seq (hcall.seq ((WXExec.wm ec).seq (WXExec.wm ee)))
    exact whole.mono (by unfold acquireSteps tailSteps;omega)
  · simp only [c,appendO,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self,hbout]
    rw [ResizeTailRequest.output,NearCubicGates.Close.Codec.frame_eq_marks,
      NearCubicWires.RepairOrdinary.Streaming.marks_append]
    rfl

end NearQuarticWires.StageNativeKidsTail
