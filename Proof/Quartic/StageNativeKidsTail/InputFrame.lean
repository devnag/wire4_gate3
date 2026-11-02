import Proof.Quartic.StageNativeKidsTail.StreamCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.Recovery.HTParts
open StageNativeKids StageResize

noncomputable def endData (f : ResizeCallee) (r : ResizeTailRequest) : WState (f.program.tapeCount+3) 5 :=
  appendO (recordsCopied f r) (inputTape f) 3 [true,false]
noncomputable def framed (f : ResizeCallee) (r : ResizeTailRequest) : WState (f.program.tapeCount+3) 5 :=
  appendO (endData f r) (inputTape f) 3 [false]
noncomputable def inputReset (f : ResizeCallee) (r : ResizeTailRequest) : WState (f.program.tapeCount+3) 5 :=
  ((framed f r).setv 3 0).seth (inputTape f) 0
noncomputable def ready (f : ResizeCallee) (r : ResizeTailRequest) : WState (f.program.tapeCount+3) 5 :=
  ((inputReset f r).setv 1 0).seth 1 0

def finishInputProgram (f : ResizeCallee) : WM (f.program.tapeCount+3) 5 :=
  .seq (emitPair (inputTape f) 3 false)
    (.seq (emitC (inputTape f) 3 false)
      (.seq (WM.rewind (inputTape f) 3) (WM.rewind 1 1)))

/-- `lem:print`, paper/paper.tex: each actual
source field contributes its literal markers to the separate input. -/
theorem recordsCopied_input (f : ResizeCallee) (r : ResizeTailRequest) :
    (recordsCopied f r).st (inputTape f)=
      marks (NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth)++marks ((inputRecords r).flatMap frame) := by
  rw [recordsCopied,adv_st_dst,(widthCopied_input f r).1]

theorem recordsCopied_head (f : ResizeCallee) (r : ResizeTailRequest) :
    (recordsCopied f r).sh (inputTape f)=
      2*(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
        2*((inputRecords r).flatMap frame).length := by
  have hsd:(1 : Fin (f.program.tapeCount+4))≠inputTape f:=(bank_off _ _).2.1.symm
  rw [recordsCopied,adv_sh_dst hsd,(widthCopied_input f r).2]
  rw [NearCubicWires.RepairOrdinary.Streaming.marks_length]

theorem recordsCopied_values (f : ResizeCallee) (r : ResizeTailRequest) :
    (recordsCopied f r).val=![2*(countWord r).length,
      (countWord r).length+(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
        ((inputRecords r).flatMap frame).length,0,
      2*(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
        2*((inputRecords r).flatMap frame).length,0] := by
  funext i
  fin_cases i <;> simp [recordsCopied,adv,appendO,widthCopied_values,
    NearCubicWires.RepairOrdinary.Streaming.marks_length]

theorem recordsCopied_sourceHead (f : ResizeCallee) (r : ResizeTailRequest) :
    (recordsCopied f r).sh 1=(countWord r).length+
      (NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
        ((inputRecords r).flatMap frame).length := by
  rw [recordsCopied,adv_sh_src,widthCopied,adv_sh_src,(counted_source f r).2]

/-- `lem:print`, paper/paper.tex: the complete
resize source closes its real delimiter and outer frame; both the
callee input and original raw source are physically rewound. -/
theorem finishInput_run (f : ResizeCallee) (r : ResizeTailRequest) :
    WExec (capacity r) (finishInputProgram f) (recordsCopied f r) (ready f r)
      (30*r.word.length+40) := by
  have hlen:=source_length r
  have hsd:(1 : Fin (f.program.tapeCount+4))≠inputTape f:=(bank_off _ _).2.1.symm
  have e1:=emitPair_spec (capacity r) (inputTape f) (3 : Fin 5) false (recordsCopied f r)
    (by rw [recordsCopied_head,recordsCopied_input,List.length_append]
        simp only [NearCubicWires.RepairOrdinary.Streaming.marks_length])
    (by rw [recordsCopied_values]
        change 2*(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
          2*((inputRecords r).flatMap frame).length+2≤capacity r
        unfold capacity;omega)
  have e2:=emitC_spec (capacity r) (inputTape f) (3 : Fin 5) false (endData f r)
    (by simp only [endData,appendO,WState.setv_sh,WState.seth_sh,WState.sets_sh,Function.update_self,
          WState.setv_st,WState.seth_st,WState.sets_st,recordsCopied_input,recordsCopied_head,
          List.length_append,List.length_cons,List.length_nil,
          NearCubicWires.RepairOrdinary.Streaming.marks_length])
    (by simp only [endData,appendO,WState.setv_val,Function.update_self,recordsCopied_values,
          List.length_cons,List.length_nil]
        change 2*(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
          2*((inputRecords r).flatMap frame).length+2<capacity r
        unfold capacity;omega)
  let L:=(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
    ((inputRecords r).flatMap frame).length+1
  have h3 : (framed f r).val 3=2*L+1 := by
    simp only [framed,endData,appendO,WState.setv_val,Function.update_self,
      List.length_cons,List.length_nil,recordsCopied_values]
    change 2*(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
      2*((inputRecords r).flatMap frame).length+2+1=2*L+1
    dsimp [L];omega
  have hh3 : (framed f r).sh (inputTape f)=2*L+1 := by
    simp only [framed,endData,appendO,WState.setv_sh,WState.seth_sh,WState.sets_sh,
      Function.update_self,List.length_cons,List.length_nil,recordsCopied_head]
    dsimp [L];omega
  have e3:=wrewind_spec (capacity r) (inputTape f) (3 : Fin 5) (2*L+1) (framed f r) h3
    (by rw [h3];unfold capacity;dsimp [L];omega)
  have e3' : WExec (capacity r) (WM.rewind (inputTape f) 3) (framed f r) (inputReset f r)
      (5*(2*L+1)+1) := by
    simpa only [inputReset,hh3,Nat.sub_self] using e3
  let K:=(countWord r).length+(NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth).length+
    ((inputRecords r).flatMap frame).length
  have h4 : (inputReset f r).val 1=K := by
    simp only [inputReset,framed,endData,appendO,WState.seth_val,WState.sets_val,WState.setv_val,
      Function.update_of_ne (by decide : (1 : Fin 5)≠3),recordsCopied_values]
    rfl
  have hh4 : (inputReset f r).sh 1=K := by
    simp only [inputReset,framed,endData,appendO,WState.seth_sh,WState.setv_sh,WState.sets_sh,
      Function.update_of_ne hsd,recordsCopied_sourceHead]
    rfl
  have e4:=wrewind_spec (capacity r) (1 : Fin (f.program.tapeCount+4)) (1 : Fin 5) K
    (inputReset f r) h4 (by rw [h4];unfold capacity;dsimp [K];omega)
  have e4' : WExec (capacity r) (WM.rewind 1 1) (inputReset f r) (ready f r) (5*K+1) := by
    simpa only [ready,hh4,Nat.sub_self] using e4
  exact (e1.seq (e2.seq (e3'.seq e4'))).mono (by dsimp [L,K];omega)

end NearQuarticWires.StageNativeKidsTail
