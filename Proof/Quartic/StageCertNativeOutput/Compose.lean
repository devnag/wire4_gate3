import Proof.Quartic.StageNativeHeader.Final
import Proof.Quartic.StageCertNative.OutputTarget
import Proof.Quartic.Program.Pipe

/-!
# The native header and the published table call, composed

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`tableWF h` is the published native-table word function `StageRecovery.NativeTableFrame.publishedWordFunction h` on
the table of a native request (the same program). `headerTableWF h` runs the native header printer
`StageNativeHeader.nativeHeaderPrinter` once and hands its output `frame r.table.word` to the table call once
(`Program.WordFunction.pipe`): it maps `r.word` to `frame r.table.output`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertNativeOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint.Downstream

/-- The budget of the header printer. -/
def headerBudget (r : NativeHeaderRequest) : ℕ :=
  10 ^ 30 * (r.parameters.n + r.table.matrix.p + 2) ^ 20 * (r.stream.length + r.table.count + 1)

/-- The budget of the table call. -/
noncomputable def tableBudget (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeHeaderRequest) : ℕ :=
  2 * StageRecovery.NativeTableFrame.steps (StageRecovery.NativeTableFrame.publishedAlgorithm h) r.table + 2

/-- **The published table call** on the table of a native request. -/
noncomputable def tableWF (h : Bindings.Williams14.Williams14_Corollary4_4) :
    WordFunction NativeHeaderRequest (fun r => r.table.word) (fun r => frame r.table.output) (tableBudget h) where
  program := (StageRecovery.NativeTableFrame.publishedWordFunction h).program
  realizes := fun r => (StageRecovery.NativeTableFrame.publishedWordFunction h).realizes r.table

/-- The budget of the composition. -/
noncomputable def htBudget (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeHeaderRequest) : ℕ :=
  4 * headerBudget r + 4 * tableBudget h r + 12

/-- **The header printer, then the table call.** -/
noncomputable def headerTableWF (h : Bindings.Williams14.Williams14_Corollary4_4) :
    WordFunction NativeHeaderRequest NativeHeaderRequest.word (fun r => frame r.table.output) (htBudget h) :=
  Program.WordFunction.pipe StageNativeHeader.nativeHeaderPrinter (tableWF h)

end NearQuarticWires.StageCertNativeOutput
