import Proof.Quartic.StageNativeKidsTail.InputFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab NearCubicGates.Close.Recovery.HTParts
open StageNativeKids StageResize

/-- `lem:print`, paper/paper.tex: the acquired
input is exactly the concrete stream-resize request's outer frame. -/
theorem ready_input (f : ResizeCallee) (r : ResizeTailRequest) :
    (ready f r).st (inputTape f)=frame r.stream.word := by
  have hs : r.stream.word=NearCubicWires.RepairRepresentation.natWord r.stream.outputWidth++
      (inputRecords r).flatMap frame++[false] := by
    unfold StreamResizeRequest.word inputRecords
    rw [fieldsRecs_eq_numberRecords]
    simp only [numberRecords,List.flatMap_map,Function.comp_def]
  simp only [ready,inputReset,WState.seth_st,WState.setv_st,framed,endData,appendO_st,
    Function.update_self,recordsCopied_input]
  rw [hs,NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
  rfl

/-- `lem:print`, paper/paper.tex: the binary
count prefix and raw source live outside the concrete resize bank. -/
theorem ready_other (f : ResizeCallee) (r : ResizeTailRequest) (i : Fin (f.program.tapeCount+4))
    (hi : i≠inputTape f) (ho : i≠out f.program.tapeCount) :
    (ready f r).st i=(loaded f r).st i := by
  simp only [ready,inputReset,WState.seth_st,WState.setv_st,framed,endData,appendO_st,
    Function.update_of_ne hi]
  rw [recordsCopied,adv_st_other _ _ _ _ hi,widthCopied,adv_st_other _ _ _ _ hi,
    counted,adv_st_other _ _ _ _ ho]

theorem ready_bank_blank (f : ResizeCallee) (r : ResizeTailRequest) (j : Fin f.program.tapeCount)
    (hj : j≠tape0 f.program) : (ready f r).st (bank f.program.tapeCount j)=[] := by
  have hi : bank f.program.tapeCount j≠inputTape f := fun he=>hj (bank_injective _ he)
  rw [ready_other f r _ hi (bank_off _ _).2.2]
  exact loaded_bank f r j

/-- `lem:print`, paper/paper.tex: every real
callee head is at zero when the single concrete resize call starts. -/
theorem ready_bank_heads (f : ResizeCallee) (r : ResizeTailRequest) (j : Fin f.program.tapeCount) :
    (ready f r).sh (bank f.program.tapeCount j)=0 := by
  have h1:= (bank_off f.program.tapeCount j).2.1
  by_cases hj:j=tape0 f.program
  · subst j
    have hi1:inputTape f≠(1 : Fin (f.program.tapeCount+4)):=(bank_off _ _).2.1
    change (ready f r).sh (inputTape f)=0
    simp only [ready,WState.seth_sh,WState.setv_sh,Function.update_of_ne hi1,
      inputReset,Function.update_self]
  · have hi : bank f.program.tapeCount j≠inputTape f := fun he=>hj (bank_injective _ he)
    have ho:bank f.program.tapeCount j≠out f.program.tapeCount:=(bank_off _ _).2.2
    simp only [ready,inputReset,WState.seth_sh,WState.setv_sh,Function.update_of_ne h1,
      Function.update_of_ne hi,framed,endData,appendO_sh,Function.update_of_ne hi]
    rw [recordsCopied,adv_sh_other _ _ _ _ hi h1,widthCopied,adv_sh_other _ _ _ _ hi h1,
      counted,adv_sh_other _ _ _ _ ho h1]
    simp only [loaded,WState.seth_sh,Function.update_of_ne (bank_off _ _).1,
      WState.sets_sh,start,idealStart]

theorem ready_values (f : ResizeCallee) (r : ResizeTailRequest) :
    (ready f r).val=![2*(countWord r).length,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [ready,inputReset,framed,endData,appendO,recordsCopied_values]

theorem ready_out (f : ResizeCallee) (r : ResizeTailRequest) :
    (ready f r).st (out f.program.tapeCount)=marks (countWord r) ∧
      (ready f r).sh (out f.program.tapeCount)=2*(countWord r).length := by
  have hi:out f.program.tapeCount≠inputTape f:=(bank_off _ _).2.2.symm
  have h1:out f.program.tapeCount≠(1 : Fin (f.program.tapeCount+4)):=out_ne_raw _
  constructor
  · simp only [ready,inputReset,WState.seth_st,WState.setv_st,framed,endData,appendO_st,
      Function.update_of_ne hi]
    rw [recordsCopied,adv_st_other _ _ _ _ hi,widthCopied,adv_st_other _ _ _ _ hi,
      counted,adv_st_dst,loaded_out,List.nil_append]
  · simp only [ready,inputReset,WState.seth_sh,WState.setv_sh,Function.update_of_ne hi,
      Function.update_of_ne h1,framed,endData,appendO_sh,Function.update_of_ne hi]
    rw [recordsCopied,adv_sh_other _ _ _ _ hi h1,widthCopied,adv_sh_other _ _ _ _ hi h1,
      counted,adv_sh_dst h1.symm,loaded_out_head]
    simp only [Nat.zero_add,NearCubicWires.RepairOrdinary.Streaming.marks_length]

theorem ready_ruler (f : ResizeCallee) (r : ResizeTailRequest) :
    (ready f r).st (ruler f.program.tapeCount)=List.replicate r.stream.budget false ∧
      (ready f r).sh (ruler f.program.tapeCount)=0 := by
  have hi:ruler f.program.tapeCount≠inputTape f:=(bank_ne_ruler _ _).symm
  have ho:ruler f.program.tapeCount≠out f.program.tapeCount := by
    intro he;have h:=congrArg Fin.val he;dsimp [ruler,out] at h;omega
  have h0:ruler f.program.tapeCount≠(0 : Fin (f.program.tapeCount+4)) := by
    intro he;have h:=congrArg Fin.val he;simp only [ruler,Fin.val_zero] at h;omega
  have h1:ruler f.program.tapeCount≠(1 : Fin (f.program.tapeCount+4)) := by
    intro he;have h:=congrArg Fin.val he;simp only [ruler,Fin.val_one] at h;omega
  constructor
  · rw [ready_other f r _ hi ho]
    simp [loaded,start,idealStart,lens,ruler,h1,h0]
  · simp only [ready,inputReset,WState.seth_sh,WState.setv_sh,Function.update_of_ne hi,
      Function.update_of_ne h1,framed,endData,appendO_sh,Function.update_of_ne hi]
    rw [recordsCopied,adv_sh_other _ _ _ _ hi h1,widthCopied,adv_sh_other _ _ _ _ hi h1,
      counted,adv_sh_other _ _ _ _ ho h1]
    simp only [loaded,WState.seth_sh,Function.update_of_ne h0,WState.sets_sh,start,idealStart]

end NearQuarticWires.StageNativeKidsTail
