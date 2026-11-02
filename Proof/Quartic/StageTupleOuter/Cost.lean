import Proof.Quartic.StagePrintTuple.TermStageContract
import Proof.Quartic.StagePrintTuple.CountedSum
import Proof.Quartic.StagePrintTuple.PreparedLoad

/-!
# The clock of the cold tuple printer

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`tupleCoreCost M r` is the clock of the core program on the prepared word: the eleven-field loader, the
initialization (three parsed scalars), the counted Terms loop (the sum of the actual monomial clocks, plus four
transitions per monomial and one final test, `countedSourceCost`), and the final counted copy of the signed cut
stream, linear in its length. `termCutBudget M Bs r` composes the preparation clock `Bs` with the core: the core is
packaged with its final rewind (`2c + 2`) and the two programs are piped (`4 b + 4 b' + 12`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.RepairOrdinary
open StageTuple

variable {B : StageNativeKids.NativeKidsRequest → ℕ}
  {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
    StageNativeKids.NativeKidsRequest.output B}
  {nativePrice : NativeStagePrice B}

/-- The clock of the core program on one request. -/
def tupleCoreCost (M : TermStageMachine native nativePrice) (r : TermCutRequest) : ℕ :=
  r.preparedLoadCost + kernelInitializeCost r + countedSourceCost (M.cost r) 0 r.terms.length +
    200 * (r.output.length + 1) + 1000

/-- The budget of the cold tuple printer: preparation, then the core with its final rewind. -/
def termCutBudget (M : TermStageMachine native nativePrice) (Bs : TermCutRequest → ℕ) (r : TermCutRequest) : ℕ :=
  4 * Bs r + 4 * (2 * tupleCoreCost M r + 2) + 12

end NearQuarticWires.StageTupleOuter
