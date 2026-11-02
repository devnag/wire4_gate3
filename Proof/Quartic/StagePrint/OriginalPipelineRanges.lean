import Proof.Quartic.StagePrint.OriginalPipelineBankFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: a fresh ordinary output is strictly inside its assigned auxiliary bank. -/
theorem firstOutput_range (second : Bool) :
    14<(firstOutput second).val ∧ (firstOutput second).val<14+firstTapes second := by
  have h0: (pipelineChildren second).program.outputTape.val≠0:=
    (pipelineChildren second).program.outputFresh
  have ht: (pipelineChildren second).program.outputTape.val<firstTapes second:=
    (pipelineChildren second).program.outputTape.isLt
  simp only [firstOutput,firstMap,if_neg h0,Fin.val_mk]
  omega

/-- `lem:print`, paper/paper.tex: the selector's output differs from its input and lies below its clock ruler. -/
theorem selectOutput_range (second : Bool) :
    15+firstTapes second<(selectOutput second).val ∧
      (selectOutput second).val<15+firstTapes second+selectTapes := by
  have h0: (pipelineSelector second).program.outputTape.val≠0:=
    (pipelineSelector second).program.outputFresh
  have ht: (pipelineSelector second).program.outputTape.val<selectTapes:=
    (pipelineSelector second).program.outputTape.isLt
  simp only [selectOutput,selectMap,Fin.val_mk]
  omega

attribute [local irreducible] firstTapes selectTapes pullTapes

/-- `lem:print`, paper/paper.tex: lower retained fields and every tape above the selector bank remain unchanged by the selector. -/
theorem selectMap_outside {second : Bool} (i : Fin (pipelineStreams second+1))
    (hi : i.val<15+firstTapes second ∨ 15+firstTapes second+selectTapes≤ i.val) :
    ∀j,selectMap second j≠i := by
  intro j h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  simp only [selectMap,Fin.val_mk] at hv
  rcases hi with hi|hi <;> omega

/-- `prop:time`, paper/paper.tex: the selector clock ruler has its exact paid initial length. -/
theorem OriginalPipelineRequest.loaded_select_ruler {second : Bool}
    (r : OriginalPipelineRequest second) :
    r.loaded.st (selectRuler second)=List.replicate r.selectBudget false := by
  have h0:15+firstTapes second+selectTapes≠13:=by omega
  have h1:15+firstTapes second+selectTapes≠14+firstTapes second:=by omega
  simp only [OriginalPipelineRequest.loaded,selectRuler,Fin.val_mk,
    dif_neg (by omega : ¬15+firstTapes second+selectTapes<13),
    OriginalPipelineRequest.lens,Fin.val_mk,if_neg h0,if_neg h1,if_pos rfl]
  simp

/-- `prop:time`, paper/paper.tex: the pullback clock ruler has its exact paid initial length. -/
theorem OriginalPipelineRequest.loaded_pull_ruler {second : Bool}
    (r : OriginalPipelineRequest second) :
    r.loaded.st (pullRuler second)=List.replicate r.pullBudget false := by
  have h0:16+firstTapes second+selectTapes+pullTapes≠13:=by omega
  have h1:16+firstTapes second+selectTapes+pullTapes≠14+firstTapes second:=by omega
  have h2:16+firstTapes second+selectTapes+pullTapes≠15+firstTapes second+selectTapes:=by omega
  simp only [OriginalPipelineRequest.loaded,pullRuler,Fin.val_mk,
    dif_neg (by omega : ¬16+firstTapes second+selectTapes+pullTapes<13),
    OriginalPipelineRequest.lens,Fin.val_mk,if_neg h0,if_neg h1,if_neg h2,if_pos rfl]
  simp

end NearQuarticWires.StagePrint
