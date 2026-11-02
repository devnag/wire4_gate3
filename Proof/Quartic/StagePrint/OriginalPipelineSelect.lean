import Proof.Quartic.StagePrint.OriginalPipelineRanges

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the original cache and retained child index are formatted into the literal row-selector request. -/
theorem originalPipelineSelect_format {second : Bool} (cap : ℕ)
    (r : OriginalPipelineRequest second) (σ : WState (pipelineStreams second) 3)
    (tapes : Fin (firstTapes second)→List Bool)
    (hd : Docked (firstMap second) r.loaded σ (fun _=>0) tapes)
    (ho : σ.st (firstOutput second)=frame r.row.original.output)
    (hcap : 4*(r.row.original.output.length+r.row.compilerIndex.val)+100≤ cap) :
    WXExec cap (writeOriginalRowInput (firstOutput second) (indexTape second)
      (selectInput second) 0 1 2) σ
      (σ.sets (selectInput second) (frame (originalRowRequest r.row.original r.row.compilerIndex).word))
      (originalRowInputCost r.row.original.output (List.replicate r.row.compilerIndex.val true)) := by
  have ha:=firstOutput_range second
  have hAB : firstOutput second≠indexTape second:=by
    intro h;have hv:=congrArg Fin.val h;simp only [indexTape,Fin.val_mk] at hv;omega
  have hAX : firstOutput second≠selectInput second:=by
    intro h;have hv:=congrArg Fin.val h;simp only [selectInput,Fin.val_mk] at hv;omega
  have hBX : indexTape second≠selectInput second:=by
    intro h;have hv:=congrArg Fin.val h;simp only [selectInput,indexTape,Fin.val_mk] at hv;omega
  have hindex : ∀j,firstMap second j≠indexTape second:=
    firstMap_outside _ (by simp [indexTape]) (Or.inl (by simp [indexTape]))
  have hinput : ∀j,firstMap second j≠selectInput second:=
    firstMap_outside _ (by simp only [selectInput,Fin.val_mk];omega) (Or.inr (by simp only [selectInput,Fin.val_mk];omega))
  have hB : σ.st (indexTape second)=frame (List.replicate r.row.compilerIndex.val true):=by
    rw [(hd.other _ hindex).1]
    rfl
  have ht : 2≤ selectTapes:=(pipelineSelector second).program.twoTapes
  have hX : σ.st (selectInput second)=[]:=by
    rw [(hd.other _ hinput).1]
    apply r.loaded_blank
    all_goals simp only [selectInput,Fin.val_mk]
    all_goals omega
  have hheads:=NearQuarticWires.StagePrint.Docked.all_heads_zero hd (fun _=>rfl)
  have hvals : σ.val=fun _=>0:=hd.val
  have e:=writeOriginalRowInput_exec cap (firstOutput second) (indexTape second)
    (selectInput second) hAB hAX hBX (0:Fin 3) 1 2 (by decide) (by decide) (by decide)
    σ r.row.original.output (List.replicate r.row.compilerIndex.val true)
    ho hB (hheads _) (hheads _) hX (hheads _) (congrFun hvals _) (congrFun hvals _)
    (congrFun hvals _) (by simpa only [List.length_replicate] using hcap)
  simpa only [originalRowRequest_word,originalRowInput] using e

end NearQuarticWires.StagePrint
