import Proof.Quartic.StagePrint.OriginalPipelineSelectorInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the real ordinary selector reads the actual formatted cache and resets its heads while returning the selected original signed row. -/
theorem originalPipelineSelector_run {second : Bool} (cap : ℕ)
    (r : OriginalPipelineRequest second) (σ : WState (pipelineStreams second) 3)
    (tapes : Fin (firstTapes second)→List Bool)
    (hd : Docked (firstMap second) r.loaded σ (fun _=>0) tapes) :
    ∃ (actual : ExecutionReceipt selectTapes (pipelineSelector second).program.stateCount)
      (τ : WState (pipelineStreams second) 3),
      actual.final.tapes (pipelineSelector second).program.outputTape=
        frame (recBits r.row.original.W
          (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val]) ∧
      WXExec cap (.machZ (pipelineSelector second).program.machine (selectMap second) (selectRuler second))
        (r.selectPrepared σ) τ (2*r.selectBudget+2) ∧
      Docked (selectMap second) (r.selectPrepared σ) τ (fun _=>0) actual.final.tapes := by
  obtain ⟨actual,hr,ho⟩:=(pipelineSelector second).realizes r
  have hin : (fun j=>(r.selectPrepared σ).st (selectMap second j))=
      (pipelineSelector second).program.inputTapes
        (originalRowRequest r.row.original r.row.compilerIndex).word:=by
    funext j
    exact r.selectPrepared_input σ tapes hd j
  rw [←hin] at hr
  have hheads:=NearQuarticWires.StagePrint.Docked.all_heads_zero hd (fun _=>rfl)
  have ht : 2≤ selectTapes:=(pipelineSelector second).program.twoTapes
  have hRI : selectRuler second≠selectInput second:=by
    intro h;have hv:=congrArg Fin.val h
    simp only [selectRuler,selectInput,Fin.val_mk] at hv
    omega
  have hclock : (r.selectPrepared σ).st (selectRuler second)=List.replicate r.selectBudget false:=by
    simp only [OriginalPipelineRequest.selectPrepared,WState.sets,Function.update_of_ne hRI]
    rw [(hd.other _ (firstMap_outside _ (by simp only [selectRuler,Fin.val_mk];omega)
      (Or.inr (by simp only [selectRuler,Fin.val_mk];omega)))).1]
    exact r.loaded_select_ruler
  have hL : ∀j,selectMap second j≠selectRuler second:=by
    intro j h
    have hv:=congrArg Fin.val h
    have hj:=j.isLt
    simp only [selectMap,selectRuler,Fin.val_mk] at hv
    omega
  obtain ⟨τ,e,dock⟩:=WXExec.machZ_run (cap:=cap) (pipelineMap_injective second).2.1 hL
    (r.selectPrepared σ) hr (fun j=>hheads _) hclock (hheads _) le_rfl
  exact ⟨actual,τ,ho,e,dock⟩

end NearQuarticWires.StagePrint
