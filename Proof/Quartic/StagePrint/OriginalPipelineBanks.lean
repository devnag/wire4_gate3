import Proof.Quartic.StagePrint.OriginalPipelineFirst

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the actual ordinary child and selector output tapes occupy fixed disjoint slots. -/
noncomputable def firstOutput (second : Bool) : Fin (pipelineStreams second+1) :=
  firstMap second (pipelineChildren second).program.outputTape
noncomputable def selectOutput (second : Bool) : Fin (pipelineStreams second+1) :=
  selectMap second (pipelineSelector second).program.outputTape
noncomputable def pullOutput (second : Bool) : Fin (pipelineStreams second+1) :=
  pullMap second (pipelinePullback second).program.outputTape

attribute [local irreducible] firstTapes selectTapes pullTapes

/-- `lem:print`, paper/paper.tex: fixed input and retained index/header slots do not depend on the gate or chosen child. -/
noncomputable def selectInput (second : Bool) : Fin (pipelineStreams second+1) :=
  ⟨15+firstTapes second,by unfold pipelineStreams;omega⟩
noncomputable def pullInput (second : Bool) : Fin (pipelineStreams second+1) :=
  ⟨16+firstTapes second+selectTapes,by unfold pipelineStreams;omega⟩
def indexTape (second : Bool) : Fin (pipelineStreams second+1) :=
  ⟨3,by unfold pipelineStreams;omega⟩
def headerTape (second : Bool) : Fin (pipelineStreams second+1) :=
  ⟨4,by unfold pipelineStreams;omega⟩

end NearQuarticWires.StagePrint
