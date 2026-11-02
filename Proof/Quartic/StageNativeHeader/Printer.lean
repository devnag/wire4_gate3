import Proof.Quartic.StageNativeHeader.Budget

/-!
# The native header printer as a word function, for an emission

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`nativeHeaderPrinterOf E` packages `mainP E` by `Expand.PolyTab.wordFunction_of_ideal`: from the framed input
`[n, r, b, s, p].flatMap natWord ++ stream`, the program prints `frame (table.word)` within
`10^30 (n+p+2)^20 (|stream| + U² + 1)` steps (`budget_le`), for every emission `E` meeting `EmitSpec` and avoiding the
output.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires.WireExponent3_5.FinalPass.Tm NearQuarticWires.Control
open NearQuarticWires.StagePrint.Downstream

/-- **The native header printer**, for an emission `E` of the marked table request. -/
noncomputable def nativeHeaderPrinterOf (E : WM hns hnr) (hE : EmitSpec E) (hEA : WM.Avoids sOUT E) :
    NativeHeaderPrinter :=
  NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (mainP E) sOUT (by simp [sOUT, strm]) runCap
    (fun _ _ => 0) runCost budget_le (fun r => ⟨rfl, main_run E hE hEA r⟩)

end NearQuarticWires.StageNativeHeader
