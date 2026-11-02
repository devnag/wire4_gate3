import Proof.Quartic.StagePrint.OriginalPipelinePullFormat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the actual first two calls leave every future affine pullback tape empty. -/
theorem OriginalPipelineRequest.afterSelector_pull_blank {second : Bool}
    (r : OriginalPipelineRequest second) (σ τ : WState (pipelineStreams second) 3)
    (t1 : Fin (firstTapes second)→List Bool) (t2 : Fin selectTapes→List Bool)
    (hd1 : Docked (firstMap second) r.loaded σ (fun _=>0) t1)
    (hd2 : Docked (selectMap second) (r.selectPrepared σ) τ (fun _=>0) t2)
    (j : Fin pullTapes) : τ.st (pullMap second j)=[] := by
  have hj:=j.isLt
  rw [originalPipelineAfterSelector_other r σ τ t1 t2 hd1 hd2 _
    (firstMap_outside _ (by simp only [pullMap,Fin.val_mk];omega)
      (Or.inr (by simp only [pullMap,Fin.val_mk];omega)))
    (selectMap_outside _ (Or.inr (by simp only [pullMap,Fin.val_mk];omega)))
    (by intro h;have hv:=congrArg Fin.val h;simp only [pullMap,selectInput,Fin.val_mk] at hv;omega)]
  apply r.loaded_blank
  all_goals simp only [pullMap,Fin.val_mk]
  all_goals omega

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the complete cold affine machine reads the actual selected original row and canonical metadata. -/
theorem originalPipelinePull_run {second : Bool} (cap : ℕ)
    (r : OriginalPipelineRequest second) (σ τ : WState (pipelineStreams second) 3)
    (t1 : Fin (firstTapes second)→List Bool) (t2 : Fin selectTapes→List Bool)
    (hd1 : Docked (firstMap second) r.loaded σ (fun _=>0) t1)
    (hd2 : Docked (selectMap second) (r.selectPrepared σ) τ (fun _=>0) t2) :
    ∃ (actual : ExecutionReceipt pullTapes (pipelinePullback second).program.stateCount)
      (out : WState (pipelineStreams second) 3),
      actual.final.tapes (pipelinePullback second).program.outputTape=r.row.canonicalPullback.output ∧
      WXExec cap (.machZ (pipelinePullback second).program.machine (pullMap second) (pullRuler second))
        (r.pullPrepared τ) out (2*r.pullBudget+2) ∧
      Docked (pullMap second) (r.pullPrepared τ) out (fun _=>0) actual.final.tapes := by
  obtain ⟨actual,hr,ho⟩:=(pipelinePullback second).realizes r
  have hin : (fun j=>(r.pullPrepared τ).st (pullMap second j))=
      (pipelinePullback second).program.inputTapes r.row.canonicalPullback.word:=by
    funext j
    exact preparedBank_input (pipelinePullback second).program τ (pullMap second)
      (pullInput second) (16+firstTapes second+selectTapes) r.row.canonicalPullback.word
      (fun _=>rfl) rfl (r.afterSelector_pull_blank σ τ t1 t2 hd1 hd2) j
  rw [←hin] at hr
  have hheads1:=NearQuarticWires.StagePrint.Docked.all_heads_zero hd1 (fun _=>rfl)
  have hheads:=NearQuarticWires.StagePrint.Docked.all_heads_zero hd2 (fun i=>hheads1 i)
  have ht : 2≤ pullTapes:=(pipelinePullback second).program.twoTapes
  have hRI : pullRuler second≠pullInput second:=by
    intro h;have hv:=congrArg Fin.val h
    simp only [pullRuler,pullInput,Fin.val_mk] at hv
    omega
  have hclock : (r.pullPrepared τ).st (pullRuler second)=List.replicate r.pullBudget false:=by
    simp only [OriginalPipelineRequest.pullPrepared,WState.sets,Function.update_of_ne hRI]
    rw [originalPipelineAfterSelector_other r σ τ t1 t2 hd1 hd2 _
      (firstMap_outside _ (by simp only [pullRuler,Fin.val_mk];omega)
        (Or.inr (by simp only [pullRuler,Fin.val_mk];omega)))
      (selectMap_outside _ (Or.inr (by simp only [pullRuler,Fin.val_mk];omega)))
      (by intro h;have hv:=congrArg Fin.val h;simp only [pullRuler,selectInput,Fin.val_mk] at hv;omega)]
    exact r.loaded_pull_ruler
  have hL : ∀j,pullMap second j≠pullRuler second:=by
    intro j h
    have hv:=congrArg Fin.val h
    have hj:=j.isLt
    simp only [pullMap,pullRuler,Fin.val_mk] at hv
    omega
  obtain ⟨out,e,dock⟩:=WXExec.machZ_run (cap:=cap) (pipelineMap_injective second).2.2.1 hL
    (r.pullPrepared τ) hr (fun j=>hheads _) hclock (hheads _) le_rfl
  exact ⟨actual,out,ho,e,dock⟩

end NearQuarticWires.StagePrint
