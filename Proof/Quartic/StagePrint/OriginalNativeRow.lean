import Proof.Quartic.StagePrint.OriginalRowCall
import Proof.Quartic.StagePullback.NativeFields
import Proof.Quartic.StagePullback.NativeSemantics
import Proof.Quartic.StagePullback.RowWordFunction
import Proof.Quartic.StagePullback.RowCost

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.TabMachine

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual selected original equation has one native dense affine child on the same two Hamming halves. -/
def OriginalRowData.nativeChild (r : OriginalRowData) :
    ExactThresholdGate
      (PrimT.C4Geo.width r.parameters+PrimT.C4Geo.width r.parameters) :=
  StagePullback.NativeRows.nativeChild r.canonicalPullback.point
    r.canonicalPullback.child r.transpose

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual affine row machine emits precisely this original child's native signed coefficient and target fields. -/
theorem OriginalRowData.native_output (r : OriginalRowData) :
    r.canonicalPullback.output=fieldsRecs r.canonicalPullback.Lout
      [List.ofFn r.nativeChild.weight++[r.nativeChild.target]] :=
  StagePullback.NativeRows.request_output_nativeChild r.canonicalPullback

/-- `imp:pullback` and `lem:print`, paper/paper.tex: all native entries evaluate the original selected equation at the literal canonical translated star corner; the certificate transpose only exchanges the two center indices. -/
theorem OriginalRowData.native_eval (r : OriginalRowData) (row column : ℕ) :
    r.nativeChild.eval
      (Pool.centerInput (PrimT.C4Geo.width r.parameters)
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.parameters) row)
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.parameters) column))=
      (Cells.childGate r.child).eval
        (StagePullback.NativeRows.affinePoint r.canonicalPullback.point
          (if r.transpose then column else row) (if r.transpose then row else column)) :=
  StagePullback.NativeRows.nativeChild_eval r.canonicalPullback.point
    r.canonicalPullback.child r.transpose row column

end NearQuarticWires.StagePrint
