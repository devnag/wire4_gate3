import Proof.Quartic.StagePrint.DownstreamTargets
import Proof.Quartic.StageRecovery.FramedNativeTable

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative.Output
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint.Downstream

/-- `lem:print`, paper/paper.tex: exact native
output is the actually computed signed reconstruction width followed
by the unchanged full signed table stream in one outer frame. -/
def output (r : NativeHeaderRequest) : List Bool :=
  frame (natWord (r.table.q+1)++r.table.output)

/-- `prop:time`, paper/paper.tex: all setup,
header generation and final framing have a fixed structural polynomial
factor and linear dependence on actual source, native census and the
existing published native-table call clock. -/
noncomputable def budget (h : Bindings.Williams14.Williams14_Corollary4_4)
    (r : NativeHeaderRequest) : ℕ :=
  10^50*(r.parameters.n+r.table.matrix.p+2)^60*
    (r.word.length+r.table.count+
      StageRecovery.NativeTableFrame.steps (StageRecovery.NativeTableFrame.publishedAlgorithm h)
        r.table+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed cold ordinary machine consumes only five
binary original scalars and actual weak cuts. The table and all shape
relations are erased correctness data, never a runtime table provider. -/
abbrev Producer (h : Bindings.Williams14.Williams14_Corollary4_4) :=
  WordFunction NativeHeaderRequest NativeHeaderRequest.word output (budget h)

end NearQuarticWires.StageCertNative.Output
