import Proof.Quartic.StageNativeHeader.Printer
import Proof.Quartic.StageNativeHeader.EmitFinal

/-!
# The native header printer

Paper: `lem:print` and `prop:time`, paper/paper.tex.

The cold printer of the native table request: from the five binary fields `n, r, b, s, p` and the raw weak cut
stream, it reads the fields, calls the sealed column printer `StageColumns.columnWordFunction`, counts the cuts at their
frame boundaries (`CutScan.countRows`), emits the header, the original cut bytes and the unary fields `q`, `U²`,
`q − 1` (`emitP`), and prints exactly `frame (table.word)` within `10^30 (n+p+2)^20 (|stream| + U² + 1)` steps.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

/-- The emission meets its specification. -/
theorem emitP_spec : EmitSpec emitP := fun r cap hcap σ h => emitP_exec r cap hcap σ h

/-- **The native header printer** (`lem:print`, paper/paper.tex). -/
noncomputable def nativeHeaderPrinter : NearQuarticWires.StagePrint.Downstream.NativeHeaderPrinter :=
  nativeHeaderPrinterOf emitP emitP_spec emitP_avoids

end NearQuarticWires.StageNativeHeader
