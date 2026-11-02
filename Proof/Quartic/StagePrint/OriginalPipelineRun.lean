import Proof.Quartic.StagePrint.OriginalPipelineProgram

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: the complete cold original-source pipeline returns the actual same-center signed affine child. -/
theorem originalPipeline_run {second : Bool} (r : OriginalPipelineRequest second) :
    ∃ out : WState (pipelineStreams second) 3,
      WXExec r.capacity (originalPipelineProgram second)
        (idealStart (pipelineStreams second) 3 r.word r.lens) out r.clock ∧
      out.st (pullOutput second)=r.row.canonicalPullback.output := by
  have e0:=originalPipelineLoad_spec r.capacity r
  obtain ⟨a1,σ,h1,e1,hd1⟩:=originalPipelineFirst_run r.capacity r
  have hc : σ.st (firstOutput second)=frame r.row.original.output:=by
    unfold firstOutput
    rw [hd1.st]
    exact h1
  have ef1:=originalPipelineSelect_format r.capacity r σ a1.final.tapes hd1 hc r.capacity_selector
  obtain ⟨a2,τ,h2,e2,hd2⟩:=originalPipelineSelector_run r.capacity r σ a1.final.tapes hd1
  have hs : τ.st (selectOutput second)=frame r.rowBody:=by
    unfold selectOutput
    rw [hd2.st]
    exact h2
  have ef2:=originalPipelinePull_format r.capacity r σ τ a1.final.tapes a2.final.tapes hd1 hd2 hs
    r.capacity_pull
  obtain ⟨a3,out,h3,e3,hd3⟩:=originalPipelinePull_run r.capacity r σ τ a1.final.tapes a2.final.tapes hd1 hd2
  have e23 := WXExec.seq ef2 e3
  have e123 := WXExec.seq e2 e23
  have e0123 := WXExec.seq ef1 e123
  have e00123 := WXExec.seq e1 e0123
  have ewhole := WXExec.seq e0 e00123
  refine ⟨out,?_,?_⟩
  · exact ewhole
  · unfold pullOutput
    rw [hd3.st]
    exact h3

end NearQuarticWires.StagePrint
