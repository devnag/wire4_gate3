import Proof.Quartic.StagePrint.OriginalPipelineRun

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the actual final output is a fresh ordinary tape rather than the original input. -/
theorem pullOutput_ne_zero (second : Bool) : (pullOutput second).val≠0 := by
  change 16+firstTapes second+selectTapes+(pipelinePullback second).program.outputTape.val≠0
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual final output starts empty and never doubles as a clock ruler. -/
theorem OriginalPipelineRequest.lens_output {second : Bool} (r : OriginalPipelineRequest second) :
    r.lens (pullOutput second)=0 := by
  have ht : (pipelinePullback second).program.outputTape.val<pullTapes:=
    (pipelinePullback second).program.outputTape.isLt
  have h0 : 16+firstTapes second+selectTapes+(pipelinePullback second).program.outputTape.val≠13:=by omega
  have h1 : 16+firstTapes second+selectTapes+(pipelinePullback second).program.outputTape.val≠14+firstTapes second:=by omega
  have h2 : 16+firstTapes second+selectTapes+(pipelinePullback second).program.outputTape.val≠15+firstTapes second+selectTapes:=by omega
  have h3 : 16+firstTapes second+selectTapes+(pipelinePullback second).program.outputTape.val≠16+firstTapes second+selectTapes+pullTapes:=by omega
  simp only [OriginalPipelineRequest.lens,pullOutput,pullMap,Fin.val_mk,
    if_neg h0,if_neg h1,if_neg h2,if_neg h3]

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: actual finite original-source bytes, original-child index and canonical metadata produce the same-center native affine row, with all loader/copy/call clocks included. -/
noncomputable def originalPipelinePrinter (second : Bool) :
    WordFunction (OriginalPipelineRequest second) OriginalPipelineRequest.word
      (fun r=>r.row.canonicalPullback.output) OriginalPipelineRequest.budget :=
  wordFunction_of_ideal (originalPipelineProgram second) (pullOutput second)
    (pullOutput_ne_zero second) OriginalPipelineRequest.capacity OriginalPipelineRequest.lens
    OriginalPipelineRequest.clock (fun _=>le_rfl) (fun r=>⟨r.lens_output,originalPipeline_run r⟩)

end NearQuarticWires.StagePrint
