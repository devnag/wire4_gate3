import Proof.Quartic.StagePrint.OriginalPipelinePullRun

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the selected signed original row has the compiler's original field width. -/
def OriginalPipelineRequest.rowBody {second : Bool} (r : OriginalPipelineRequest second) : List Bool :=
  recBits r.row.original.W (compileL r.row.original.weights r.row.original.target)[r.row.compilerIndex.val]

/-- `prop:time`, paper/paper.tex: both actual request formatters retain their literal copy and rewind clocks. -/
def OriginalPipelineRequest.selectorFormatCost {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  originalRowInputCost r.row.original.output (List.replicate r.row.compilerIndex.val true)
def OriginalPipelineRequest.pullFormatCost {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  pullbackInputCost (r.row.header r.row.fields_fit) r.rowBody

/-- `prop:time`, paper/paper.tex: one explicit binary-register capacity covers both actual request copies. -/
def OriginalPipelineRequest.capacity {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  1000*(r.row.original.output.length+r.row.compilerIndex.val+
    (r.row.header r.row.fields_fit).length+r.rowBody.length+1)

/-- `prop:time`, paper/paper.tex: the clock sums the cold loader, three actual ordinary calls, both paid copy/rewind phases, and all five sequence transitions. -/
noncomputable def OriginalPipelineRequest.clock {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  r.loadCost+1+(2*r.source.childrenBudget+2+1+
    (r.selectorFormatCost+1+(2*r.selectBudget+2+1+(r.pullFormatCost+1+(2*r.pullBudget+2)))))
noncomputable def OriginalPipelineRequest.budget {second : Bool} (r : OriginalPipelineRequest second) : ℕ :=
  2*r.clock+2

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: cold original decomposition precedes child selection and the actual same-center affine row machine. -/
noncomputable def originalPipelineProgram (second : Bool) : WMX (pipelineStreams second) 3 :=
  .seq (.mach Top.loadM (pipelineLoadMap second))
    (.seq (.machZ (pipelineChildren second).program.machine (firstMap second) (firstRuler second))
      (.seq (writeOriginalRowInput (firstOutput second) (indexTape second) (selectInput second) 0 1 2)
        (.seq (.machZ (pipelineSelector second).program.machine (selectMap second) (selectRuler second))
          (.seq (writePullbackInput (headerTape second) (selectOutput second) (pullInput second) 0 1 2)
            (.machZ (pipelinePullback second).program.machine (pullMap second) (pullRuler second))))))

/-- `prop:time`, paper/paper.tex: the first formatter's actual byte counts fit its declared capacity. -/
theorem OriginalPipelineRequest.capacity_selector {second : Bool} (r : OriginalPipelineRequest second) :
    4*(r.row.original.output.length+r.row.compilerIndex.val)+100≤ r.capacity := by
  unfold OriginalPipelineRequest.capacity
  omega

/-- `prop:time`, paper/paper.tex: the second formatter's actual byte counts fit the same declared capacity. -/
theorem OriginalPipelineRequest.capacity_pull {second : Bool} (r : OriginalPipelineRequest second) :
    4*((r.row.header r.row.fields_fit).length+r.rowBody.length)+4≤ r.capacity := by
  unfold OriginalPipelineRequest.capacity
  omega

end NearQuarticWires.StagePrint
