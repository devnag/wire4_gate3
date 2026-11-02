import Proof.Quartic.StagePrint.OriginalPipelineLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab


/-- `lem:print`, paper/paper.tex: the original occurrence machine receives exactly the actually loaded finite original call and index, on its real tape zero. -/
theorem OriginalPipelineRequest.first_input {second : Bool} (r : OriginalPipelineRequest second)
    (j : Fin (firstTapes second)) :
    r.loaded.st (firstMap second j)=(pipelineChildren second).program.inputTapes r.source.source j := by
  by_cases hj : j.val=0
  · simp [OriginalPipelineRequest.loaded,OriginalPipelineRequest.fields,firstMap,hj,Program.inputTapes]
  · have h13 : ¬14+j.val<13:=by omega
    have he13 : 14+j.val≠13:=by omega
    have he1 : 14+j.val≠14+firstTapes second:=by have:=j.isLt;omega
    have he1a : j.val≠firstTapes second:=Nat.ne_of_lt j.isLt
    have he2 : 14+j.val≠15+firstTapes second+selectTapes:=by have:=j.isLt;omega
    have he3 : 14+j.val≠16+firstTapes second+selectTapes+pullTapes:=by have:=j.isLt;omega
    simp [OriginalPipelineRequest.loaded,firstMap,hj,h13,OriginalPipelineRequest.lens,
      he13,he1,he1a,he2,he3,Program.inputTapes]

/-- `prop:time`, paper/paper.tex: the original-call compiler's real clock is stored only on its dedicated blank ruler. -/
theorem OriginalPipelineRequest.first_ruler {second : Bool} (r : OriginalPipelineRequest second) :
    r.loaded.st (firstRuler second)=List.replicate r.source.childrenBudget false := by
  have h13 : ¬14+firstTapes second<13:=by omega
  have he13 : 14+firstTapes second≠13:=by omega
  simp [OriginalPipelineRequest.loaded,firstRuler,h13,OriginalPipelineRequest.lens,he13]

/-- `lem:print`, paper/paper.tex: the actual first call bank is disjoint from its ordinary-machine ruler. -/
theorem firstMap_ne_ruler (second : Bool) (j : Fin (firstTapes second)) :
    firstMap second j≠firstRuler second := by
  intro h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  unfold firstMap firstRuler at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> omega

/-- `lem:print`, paper/paper.tex: the complete original disjoint-child compiler actually runs on the retained finite source, returning its true framed cache with every ordinary tape head reset. -/
theorem originalPipelineFirst_run {second : Bool} (cap : ℕ) (r : OriginalPipelineRequest second) :
    ∃ (actual : ExecutionReceipt (firstTapes second) (pipelineChildren second).program.stateCount)
      (τ : WState (pipelineStreams second) 3),
      actual.final.tapes (pipelineChildren second).program.outputTape=frame r.row.original.output ∧
      WXExec cap (.machZ (pipelineChildren second).program.machine (firstMap second) (firstRuler second))
        r.loaded τ (2*r.source.childrenBudget+2) ∧
      Docked (firstMap second) r.loaded τ (fun _=>0) actual.final.tapes := by
  obtain ⟨actual,hr,ho⟩:=(pipelineChildren second).realizes r
  have hin : (fun j=>r.loaded.st (firstMap second j))=
      (pipelineChildren second).program.inputTapes r.source.source:=by
    funext j
    exact r.first_input j
  rw [←hin] at hr
  obtain ⟨τ,e,dock⟩:=WXExec.machZ_run (cap:=cap) (pipelineMap_injective second).1
    (firstMap_ne_ruler second) r.loaded hr (fun _=>rfl) r.first_ruler rfl le_rfl
  exact ⟨actual,τ,ho,e,dock⟩

end NearQuarticWires.StagePrint
