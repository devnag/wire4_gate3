import Proof.Quartic.StageEqualityRows.Formatter
import Proof.Quartic.StageEqualityRows.StripData

set_option autoImplicit false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint StagePrint.Downstream

def constructionBudget (r : NativeStreamRequest) : ℕ :=
  4*(2*formatterSteps r+2)+4*r.equalityBudget+12

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold equality count feeds the original
signed two-cut constructor at its literal physical clock, separately
for each walk's own row stream. -/
noncomputable def constructionWordFunction :
    WordFunction NativeStreamRequest equalityRowsInput (fun r=>frame (temporaryWord r)) constructionBudget :=
  Program.WordFunction.pipe formatterWordFunction nativeEqualityPrinter

end NearQuarticWires.StageEqualityRows
