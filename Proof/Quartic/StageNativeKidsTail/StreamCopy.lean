import Proof.Quartic.StageNativeKidsTail.CountCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.Recovery.HTParts
open StageNativeKids StageResize StageTuple

theorem source_length (r : ResizeTailRequest) :
    r.word.length=(countWord r).length+(natWord r.stream.outputWidth).length+
      ((inputRecords r).flatMap frame).length+1 := by
  rw [source_shape]
  simp only [List.length_append,List.length_cons,List.length_nil]

def inputTape (f : ResizeCallee) : Fin (f.program.tapeCount+4) :=
  bank f.program.tapeCount (tape0 f.program)

noncomputable def widthCopied (f : ResizeCallee) (r : ResizeTailRequest) :
    WState (f.program.tapeCount+3) 5 :=
  adv 1 (inputTape f) 3 1 (counted f r) (marks (natWord r.stream.outputWidth))
    (natWord r.stream.outputWidth).length

noncomputable def recordsCopied (f : ResizeCallee) (r : ResizeTailRequest) :
    WState (f.program.tapeCount+3) 5 :=
  adv 1 (inputTape f) 3 1 (widthCopied f r) (marks ((inputRecords r).flatMap frame))
    ((inputRecords r).flatMap frame).length

theorem counted_input (f : ResizeCallee) (r : ResizeTailRequest) :
    (counted f r).st (inputTape f)=[] ∧ (counted f r).sh (inputTape f)=0 := by
  have hio:inputTape f≠out f.program.tapeCount:=(bank_off _ _).2.2
  have hir:inputTape f≠(1 : Fin (f.program.tapeCount+4)):=(bank_off _ _).2.1
  have hi0:inputTape f≠(0 : Fin (f.program.tapeCount+4)):=(bank_off _ _).1
  constructor
  · rw [counted,adv_st_other _ _ _ _ hio]
    exact loaded_bank f r _
  · rw [counted,adv_sh_other _ _ _ _ hio hir]
    simp only [loaded,WState.seth_sh,WState.sets_sh,Function.update_of_ne hi0,start,idealStart]

theorem counted_values (f : ResizeCallee) (r : ResizeTailRequest) :
    (counted f r).val=![2*(countWord r).length,(countWord r).length,0,0,0] := by
  funext i
  fin_cases i <;> simp [counted,adv,appendO,loaded,start,idealStart,
    NearCubicWires.RepairOrdinary.Streaming.marks_length]

theorem counted_source (f : ResizeCallee) (r : ResizeTailRequest) :
    (counted f r).st 1=r.word ∧ (counted f r).sh 1=(countWord r).length := by
  constructor
  · simp only [counted,adv_st_src (out_ne_raw _).symm,loaded,WState.seth_st,
      WState.sets_st,Function.update_self]
  · simp [counted,adv_sh_src,loaded,start,idealStart]

/-- `lem:print`, paper/paper.tex: the actual
stream width remains binary when copied into the separate concrete
resize input, after preserving the original child count. -/
theorem copyWidth_run (f : ResizeCallee) (r : ResizeTailRequest) :
    WExec (capacity r) (copyNaturalFields 1 1 (inputTape f) 3 1 2) (counted f r) (widthCopied f r)
      (28*(natWord r.stream.outputWidth).length+1) := by
  have hlen:=source_length r
  have hsd:(1 : Fin (f.program.tapeCount+4))≠inputTape f:=(bank_off _ _).2.1.symm
  have e:=copyNaturalFields_spec (capacity r) (1 : Fin (f.program.tapeCount+4)) (inputTape f)
    3 1 2 hsd (by decide) (by decide) (by decide) [r.stream.outputWidth]
    (countWord r) ((inputRecords r).flatMap frame++[false]) (counted f r)
    (by rw [(counted_source f r).1,source_shape]
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc])
    (counted_source f r).2
    (by rw [(counted_input f r).1,(counted_input f r).2];rfl)
    (by rw [counted_values];rfl)
    (by simp only [counted_values,List.flatMap_cons,List.flatMap_nil,List.append_nil]
        change 0+2*(natWord r.stream.outputWidth).length≤capacity r
        unfold capacity;omega)
    (by simp only [counted_values,List.flatMap_cons,List.flatMap_nil,List.append_nil]
        change (countWord r).length+(natWord r.stream.outputWidth).length<capacity r+1
        unfold capacity;omega)
  simpa only [widthCopied,List.length_singleton,List.flatMap_cons,List.flatMap_nil,List.append_nil] using e

theorem widthCopied_input (f : ResizeCallee) (r : ResizeTailRequest) :
    (widthCopied f r).st (inputTape f)=marks (natWord r.stream.outputWidth) ∧
      (widthCopied f r).sh (inputTape f)=2*(natWord r.stream.outputWidth).length := by
  have hsd:(1 : Fin (f.program.tapeCount+4))≠inputTape f:=(bank_off _ _).2.1.symm
  constructor
  · simp only [widthCopied,adv_st_dst,(counted_input f r).1,List.nil_append]
  · simp only [widthCopied,adv_sh_dst hsd,(counted_input f r).2,
      NearCubicWires.RepairOrdinary.Streaming.marks_length,Nat.zero_add]

theorem widthCopied_values (f : ResizeCallee) (r : ResizeTailRequest) :
    (widthCopied f r).val=![2*(countWord r).length,
      (countWord r).length+(natWord r.stream.outputWidth).length,0,
        2*(natWord r.stream.outputWidth).length,0] := by
  funext i
  fin_cases i <;> simp [widthCopied,adv,appendO,counted_values,
    NearCubicWires.RepairOrdinary.Streaming.marks_length]

/-- `lem:print`, paper/paper.tex: actual
nonempty signed-field frames are copied to the new input until their
real final delimiter, independently of empty inner row boundaries. -/
theorem copyRecords_run (f : ResizeCallee) (r : ResizeTailRequest) :
    WExec (capacity r) (CounterAsm.frameLoop 1 1 (fun b=>emitPair (inputTape f) 3 b))
      (widthCopied f r) (recordsCopied f r)
      (100*(((inputRecords r).flatMap frame).length+1)) := by
  have hlen:=source_length r
  have hsd:(1 : Fin (f.program.tapeCount+4))≠inputTape f:=(bank_off _ _).2.1.symm
  have e:=CounterAsm.frameLoop_spec (capacity r) hsd (show (3 : Fin 5)≠1 by decide)
    (emits_pair (cap:=capacity r) (dst:=inputTape f) (OP:=(3 : Fin 5))) (d:=2) (by intro b;simp)
    [false] rfl (inputRecords r) (countWord r++natWord r.stream.outputWidth) (widthCopied f r)
    (inputRecords_nonempty r)
    (by rw [widthCopied,adv_st_src hsd,(counted_source f r).1,source_shape])
    (by simp only [widthCopied,adv_sh_src,(counted_source f r).2,List.length_append])
    (by rw [(widthCopied_input f r).1,(widthCopied_input f r).2]
        simp only [NearCubicWires.RepairOrdinary.Streaming.marks_length])
    (by rw [widthCopied_values]
        change 2*(natWord r.stream.outputWidth).length+2*((inputRecords r).flatMap frame).length≤capacity r
        unfold capacity;omega)
    (by rw [widthCopied_values]
        change (countWord r).length+(natWord r.stream.outputWidth).length+
          ((inputRecords r).flatMap frame).length<capacity r+1
        unfold capacity;omega)
  exact e.mono (by omega)

end NearQuarticWires.StageNativeKidsTail
