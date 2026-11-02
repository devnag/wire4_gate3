import Proof.Quartic.StageNativeKidsPool.Full
import Proof.Quartic.StageNativeKidsPool.Budget

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open StageNativeKids StageNativeKidsPrice StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: the
first actual bank source physically computes its original child count,
prints every original native row in order and hands the literal count,
width and raw records to the existing once-only resize finalizer. -/
noncomputable def firstPoolWordFunction :
    WordFunction FirstBankRequest firstPoolWord
      (fun q=>frame q.val.resizeTailRequest.word) firstPoolBudget := by
  let F : FirstBankRequest→Family (OriginalPipelineRequest false) (fun r=>r.word):=fun q=>firstFamily q
  let f:=poolWordFunction F (fun q=>q.val.outputWidth) firstCounter
    (pipelineRecordPrinter false) (fun r=>pipelineRecords_nonempty r)
  refine ⟨f.program,?_⟩
  intro q
  obtain ⟨actual,hr,ho⟩:=f.realizes q
  have hi : sourceWord F (fun q=>q.val.outputWidth) q=firstPoolWord q:=by
    simp only [sourceWord,F,firstPoolWord,firstFamily,actualFamily,SourceCase.source,firstCountSource,
      RawBits.IndexedCallGateRequest.source,List.append_nil]
  have hb : 2*fullSteps F (fun q=>q.val.outputWidth) firstCountBudget
      OriginalPipelineRequest.budget pipelineRecords q+2=firstPoolBudget q:=rfl
  have hout : frame (answer (F q) pipelineRecords q.val.outputWidth)=
      frame q.val.resizeTailRequest.word:=by
    exact congrArg frame (actualAnswer_eq ⟨q.val,false,q.property⟩)
  rw [hi,hb] at hr
  exact ⟨actual,hr,ho.trans hout⟩

/-- `lem:print`, paper/paper.tex: the
second actual bank performs the same concrete count and ordered native
row construction after only its original occurrence offset changes;
no count, child, row cache or pool is supplied by the caller. -/
noncomputable def secondPoolWordFunction :
    WordFunction SecondBankRequest secondPoolWord
      (fun q=>frame q.val.resizeTailRequest.word) secondPoolBudget := by
  let F : SecondBankRequest→Family (OriginalPipelineRequest true) (fun r=>r.word):=fun q=>secondFamily q
  let f:=poolWordFunction F (fun q=>q.val.outputWidth) secondCounter
    (pipelineRecordPrinter true) (fun r=>pipelineRecords_nonempty r)
  refine ⟨f.program,?_⟩
  intro q
  obtain ⟨actual,hr,ho⟩:=f.realizes q
  have hi : sourceWord F (fun q=>q.val.outputWidth) q=secondPoolWord q:=by
    simp only [sourceWord,F,secondPoolWord,secondFamily,actualFamily,SourceCase.source,secondCountSource,
      RawBits.IndexedCallGateRequest.source,List.append_nil]
  have hb : 2*fullSteps F (fun q=>q.val.outputWidth) secondCountBudget
      OriginalPipelineRequest.budget pipelineRecords q+2=secondPoolBudget q:=rfl
  have hout : frame (answer (F q) pipelineRecords q.val.outputWidth)=
      frame q.val.resizeTailRequest.word:=by
    exact congrArg frame (actualAnswer_eq ⟨q.val,true,q.property⟩)
  rw [hi,hb] at hr
  exact ⟨actual,hr,ho.trans hout⟩

end NearQuarticWires.StageNativeKidsPool
