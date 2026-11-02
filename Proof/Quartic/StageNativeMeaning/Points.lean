import Proof.Quartic.StagePrint.NativeMeaningInterface
import Proof.Quartic.StagePrint.RoleSemantics

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Tabulator
open StagePrint StagePrint.NativeMeaning

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the actual row request uses exactly the original indexed
walk's numeric role point, with the certificate transpose applied once. -/
theorem originalRow_point (r : StageTuple.RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (callAtoms r.header.call (r.originalIndex i))).length)
    (row column : ℕ) :
    StagePullback.NativeRows.affinePoint (r.originalRow i j).canonicalPullback.point column row =
      Header.numericRolePoint r.header.prepared.starParams (actualWalk r) (r.role i)
        (PrimT.C4Geo.centerAt r.header.prepared.starParams
          (Builder.translation r.header.call r.header.prepared r.header.witness) column row) := by
  funext x
  simp only [StagePullback.NativeRows.affinePoint, Header.numericRolePoint,
    StageTuple.RowContext.originalRow, OriginalRowData.canonicalPullback,
    OriginalRowData.pullback, StagePullback.RowRequest.point,
    StagePullback.NativeRows.leftError, StagePullback.NativeRows.rightError,
    actualWalk, StageTuple.RowContext.role, Equiv.apply_symm_apply]
  rfl

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the printer's two native half assignments are precisely
the dense child's two custom-Phi assignment words. -/
theorem outerPoint_centerInput (width row column : ℕ) :
    outerPoint (width+width) row column = Pool.centerInput width row column := by
  funext x
  have h : (width+width+1)/2 = width := by omega
  simp only [outerPoint, Pool.centerInput, h]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: one actual native original child evaluates its original
selected equation at the literal numeric role point on the same Phi. -/
theorem originalRow_eval (r : StageTuple.RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (callAtoms r.header.call (r.originalIndex i))).length)
    (row column : ℕ) :
    (r.originalRow i j).nativeChild.eval (Pool.centerInput
      (PrimT.C4Geo.width r.header.prepared.starParams)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column)) =
      (Cells.childGate ((exactChildren (callAtoms r.header.call (r.originalIndex i)))[j.val])).eval
        (Header.numericRolePoint r.header.prepared.starParams (actualWalk r) (r.role i)
          (PrimT.C4Geo.centerAt r.header.prepared.starParams
            (Builder.translation r.header.call r.header.prepared r.header.witness) column row)) := by
  have hv := OriginalRowData.native_eval (r.originalRow i j) row column
  have htr : (r.originalRow i j).transpose = true := rfl
  simp only [htr, if_true] at hv
  rw [originalRow_point] at hv
  exact hv

end NearQuarticWires.StageNativeMeaning
