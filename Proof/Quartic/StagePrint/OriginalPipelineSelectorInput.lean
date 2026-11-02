import Proof.Quartic.StagePrint.OriginalPipelineSelect
import Proof.Quartic.StagePrint.PreparedBank

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the formatter changes only the selector's actual input stream. -/
noncomputable def OriginalPipelineRequest.selectPrepared {second : Bool}
    (r : OriginalPipelineRequest second) (σ : WState (pipelineStreams second) 3) :=
  σ.sets (selectInput second) (frame (originalRowRequest r.row.original r.row.compilerIndex).word)

/-- `lem:print`, paper/paper.tex: every selector bank tape was blank after the first disjoint-child call. -/
theorem OriginalPipelineRequest.first_select_blank {second : Bool}
    (r : OriginalPipelineRequest second) (σ : WState (pipelineStreams second) 3)
    (tapes : Fin (firstTapes second)→List Bool)
    (hd : Docked (firstMap second) r.loaded σ (fun _=>0) tapes)
    (j : Fin selectTapes) : σ.st (selectMap second j)=[] := by
  have hj:=j.isLt
  rw [(hd.other _ (firstMap_outside _ (by simp only [selectMap,Fin.val_mk];omega)
    (Or.inr (by simp only [selectMap,Fin.val_mk];omega)))).1]
  apply r.loaded_blank
  all_goals simp only [selectMap,Fin.val_mk]
  all_goals omega

/-- `lem:print`, paper/paper.tex: the physically formatted source is precisely the actual selector input bank. -/
theorem OriginalPipelineRequest.selectPrepared_input {second : Bool}
    (r : OriginalPipelineRequest second) (σ : WState (pipelineStreams second) 3)
    (tapes : Fin (firstTapes second)→List Bool)
    (hd : Docked (firstMap second) r.loaded σ (fun _=>0) tapes)
    (j : Fin selectTapes) :
    (r.selectPrepared σ).st (selectMap second j)=
      (pipelineSelector second).program.inputTapes
        (originalRowRequest r.row.original r.row.compilerIndex).word j := by
  exact preparedBank_input (pipelineSelector second).program σ (selectMap second)
    (selectInput second) (15+firstTapes second)
    (originalRowRequest r.row.original r.row.compilerIndex).word (fun _=>rfl) rfl
    (r.first_select_blank σ tapes hd) j

end NearQuarticWires.StagePrint
