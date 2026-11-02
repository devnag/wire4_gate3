import Proof.Quartic.StagePrint.OriginalPipelineSelectorRun

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the next input stream contains the actual affine metadata followed by the actual selected original signed row. -/
noncomputable def OriginalPipelineRequest.pullPrepared {second : Bool}
    (r : OriginalPipelineRequest second) (τ : WState (pipelineStreams second) 3) :=
  τ.sets (pullInput second) (frame r.row.canonicalPullback.word)

/-- `lem:print`, paper/paper.tex: the two completed ordinary calls preserve every future pullback tape and the original affine header. -/
theorem originalPipelineAfterSelector_other {second : Bool}
    (r : OriginalPipelineRequest second) (σ τ : WState (pipelineStreams second) 3)
    (t1 : Fin (firstTapes second)→List Bool) (t2 : Fin selectTapes→List Bool)
    (hd1 : Docked (firstMap second) r.loaded σ (fun _=>0) t1)
    (hd2 : Docked (selectMap second) (r.selectPrepared σ) τ (fun _=>0) t2)
    (i : Fin (pipelineStreams second+1))
    (hi1 : ∀j,firstMap second j≠i) (hi2 : ∀j,selectMap second j≠i)
    (hiX : i≠selectInput second) : τ.st i=r.loaded.st i := by
  rw [(hd2.other i hi2).1]
  simp only [OriginalPipelineRequest.selectPrepared,WState.sets,Function.update_of_ne hiX]
  exact (hd1.other i hi1).1

/-- `lem:print`, paper/paper.tex: actual header and selected-row bytes are joined before the affine pullback call. -/
theorem originalPipelinePull_format {second : Bool} (cap : ℕ)
    (r : OriginalPipelineRequest second) (σ τ : WState (pipelineStreams second) 3)
    (t1 : Fin (firstTapes second)→List Bool) (t2 : Fin selectTapes→List Bool)
    (hd1 : Docked (firstMap second) r.loaded σ (fun _=>0) t1)
    (hd2 : Docked (selectMap second) (r.selectPrepared σ) τ (fun _=>0) t2)
    (ho : τ.st (selectOutput second)=frame (recBits r.row.original.W
      (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val]))
    (hcap : 4*((r.row.header r.row.fields_fit).length+
      (recBits r.row.original.W
        (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val]).length)+4≤ cap) :
    WXExec cap (writePullbackInput (headerTape second) (selectOutput second) (pullInput second) 0 1 2)
      τ (r.pullPrepared τ)
      (pullbackInputCost (r.row.header r.row.fields_fit)
        (recBits r.row.original.W
          (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val])) := by
  have ha:=selectOutput_range second
  have ht : 2≤ pullTapes:=(pipelinePullback second).program.twoTapes
  have hAB : headerTape second≠selectOutput second:=by
    intro h;have hv:=congrArg Fin.val h;simp only [headerTape,Fin.val_mk] at hv;omega
  have hAX : headerTape second≠pullInput second:=by
    intro h;have hv:=congrArg Fin.val h;simp only [headerTape,pullInput,Fin.val_mk] at hv;omega
  have hBX : selectOutput second≠pullInput second:=by
    intro h;have hv:=congrArg Fin.val h;simp only [pullInput,Fin.val_mk] at hv;omega
  have hA : τ.st (headerTape second)=frame (r.row.header r.row.fields_fit):=by
    rw [originalPipelineAfterSelector_other r σ τ t1 t2 hd1 hd2 _
      (firstMap_outside _ (by simp [headerTape]) (Or.inl (by simp [headerTape])))
      (selectMap_outside _ (Or.inl (by simp only [headerTape,Fin.val_mk];omega)))
      (by intro h;have hv:=congrArg Fin.val h;simp only [headerTape,selectInput,Fin.val_mk] at hv;omega)]
    rfl
  have hX : τ.st (pullInput second)=[]:=by
    rw [originalPipelineAfterSelector_other r σ τ t1 t2 hd1 hd2 _
      (firstMap_outside _ (by simp only [pullInput,Fin.val_mk];omega)
        (Or.inr (by simp only [pullInput,Fin.val_mk];omega)))
      (selectMap_outside _ (Or.inr (by simp only [pullInput,Fin.val_mk];omega)))
      (by intro h;have hv:=congrArg Fin.val h;simp only [pullInput,selectInput,Fin.val_mk] at hv;omega)]
    apply r.loaded_blank
    all_goals simp only [pullInput,Fin.val_mk]
    all_goals omega
  have hheads1:=NearQuarticWires.StagePrint.Docked.all_heads_zero hd1 (fun _=>rfl)
  have hheads:=NearQuarticWires.StagePrint.Docked.all_heads_zero hd2 (fun i=>hheads1 i)
  have hvals : τ.val=fun _=>0:=hd2.val.trans hd1.val
  have e:=writePullbackInput_exec cap (headerTape second) (selectOutput second) (pullInput second)
    hAB hAX hBX (0:Fin 3) 1 2 (by decide) (by decide) (by decide) τ
    (r.row.header r.row.fields_fit)
    (recBits r.row.original.W (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val])
    hA ho (hheads _) (hheads _) hX (hheads _) (congrFun hvals _) (congrFun hvals _)
    (congrFun hvals _) hcap
  simpa only [r.row.canonicalPullback_word,OriginalPipelineRequest.pullPrepared] using e

end NearQuarticWires.StagePrint
