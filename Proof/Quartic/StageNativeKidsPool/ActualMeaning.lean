import Proof.Quartic.StageNativeKidsPool.Budget

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open StageNativeKids StageNativeKidsPrice StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: the
computed increasing row loop follows the actual finite interval of
indices and concatenates their raw bytes in that order. -/
theorem suffix_range (bytes : ℕ→List Bool) (j left : ℕ) :
    suffix bytes j left=(List.range' j left).flatMap bytes := by
  induction left generalizing j with
  | zero=>rfl
  | succ left ih=>simp only [suffix,List.range'_succ,List.flatMap_cons,ih]

/-- `lem:print`, paper/paper.tex: the
complete counted suffix equals the original finite row-family list,
including count zero and unchanged duplicate occurrence positions. -/
theorem Family.full_bytes {R : Type} {input : R→List Bool}
    (F : Family R input) (records : R→List (List Bool)) :
    suffix (F.bytes records) 0 F.count=
      (List.ofFn fun j : Fin F.count=>(records (F.request j)).flatMap frame).flatten := by
  rw [suffix_range,←List.range_eq_range',List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hlt : i<F.count:=by simpa using hi
  simp [Family.bytes,hlt]

/-- `lem:print`, paper/paper.tex: the
cold counted-pool output is precisely the existing resize-tail source,
with actual count, target-width bytes, original native rows and delimiter. -/
theorem actualAnswer_eq (a : SourceCase) : actualAnswer a=a.request.resizeTailRequest.word := by
  rw [actualAnswer,Family.full_bytes]
  change natWord (actualFamily a).count++natWord a.request.outputWidth++
    (List.ofFn fun j : Children a=>(pipelineRecords (rowRequest a j)).flatMap frame).flatten++[false]=_
  rw [rows_output,resizeTailRequest_word]
  simp only [actualFamily,RowContext.nativeKids_length,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the
first actual bank's row family retains its exact original source case. -/
def firstFamily (q : FirstBankRequest) :=actualFamily ⟨q.val,false,q.property⟩

/-- `lem:print`, paper/paper.tex: the
second actual bank's row family uses only the actual occurrence offset. -/
def secondFamily (q : SecondBankRequest) :=actualFamily ⟨q.val,true,q.property⟩

/-- `lem:print`, paper/paper.tex: the
existing actual first-bank counter computes the generated row-family
count, without an additional count or selected-row input. -/
noncomputable def firstCounter :
    WordFunction FirstBankRequest (fun q=>(firstFamily q).source)
      (fun q=>frame (natWord (firstFamily q).count)) firstCountBudget :=
  ⟨firstCountWordFunction.program,by
    intro q
    simpa only [firstFamily,actualFamily,SourceCase.source,firstCountSource,
      RawBits.IndexedCallGateRequest.source,List.append_nil,RowContext.nativeKids_length]
      using firstCountWordFunction.realizes q⟩

/-- `lem:print`, paper/paper.tex: the
same actual original compiler computes the second row-family count
with the true relative occurrence and all threshold ties preserved. -/
noncomputable def secondCounter :
    WordFunction SecondBankRequest (fun q=>(secondFamily q).source)
      (fun q=>frame (natWord (secondFamily q).count)) secondCountBudget :=
  ⟨secondCountWordFunction.program,by
    intro q
    simpa only [secondFamily,actualFamily,SourceCase.source,secondCountSource,
      RawBits.IndexedCallGateRequest.source,List.append_nil,RowContext.nativeKids_length]
      using secondCountWordFunction.realizes q⟩

end NearQuarticWires.StageNativeKidsPool
