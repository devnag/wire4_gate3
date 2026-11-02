import Proof.Quartic.StageNativeMeaning.Points
import Proof.Quartic.StagePrint.CenterCoordinates
import Proof.Quartic.StagePrint.CenterPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open StagePrint StagePrint.NativeMeaning

/-- `sec:walks` and `lem:print`, paper/paper.tex: the physical low-first walk is exactly the original
Builder pattern decoder, with no supplied reindexing map. -/
theorem actualWalk_eq (r : StageTuple.RowContext) :
    actualWalk r = callPatterns r.header.call r.header.prepared
      (indexedWalk r.header.prepared.seedParameters.N r.walkCode) := rfl

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every literal physical native atom is the actual original
walk atom on the same translated center, including padded entries. -/
theorem actualAtom_walkAtomPoint (r : StageTuple.RowContext) (row column : ℕ) :
    actualAtom r row column = Cells.walkAtomPoint r.header.prepared.starParams (by decide : 0<4)
      (callPatterns r.header.call r.header.prepared
        (indexedWalk r.header.prepared.seedParameters.N r.walkCode))
      (callAtoms r.header.call)
      (PrimT.C4Geo.centerAt r.header.prepared.starParams
        (Builder.translation r.header.call r.header.prepared r.header.witness) column row) := by
  funext i
  exact congrArg (callAtoms r.header.call (r.originalIndex i)).eval
    (Header.numericRolePoint_eq r.header.prepared.starParams (actualWalk r) (r.role i)
      (PrimT.C4Geo.centerAt r.header.prepared.starParams
        (Builder.translation r.header.call r.header.prepared r.header.witness) column row))

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: native high-row/low-column
order is the actual original Builder center index, with the transpose
applied once and no permutation of the retained original columns. -/
theorem actualAtom_centerIndex (r : StageTuple.RowContext)
    (row : Fin (2^PrimT.C4Geo.dR r.header.prepared.starParams))
    (column : Fin (2^PrimT.C4Geo.dRow r.header.prepared.starParams)) :
    actualAtom r row.val column.val =
      Cells.walkAtomPoint r.header.prepared.starParams (by decide : 0<4)
        (callPatterns r.header.call r.header.prepared
          (indexedWalk r.header.prepared.seedParameters.N r.walkCode))
        (callAtoms r.header.call)
        (Builder.center r.header.call r.header.prepared r.header.witness
          (centerIndex r.header.call r.header.prepared column row)) := by
  have h := centerIndex_point r.header.call r.header.prepared r.header.witness column row
  exact (actualAtom_walkAtomPoint r row.val column.val).trans
    (congrArg (Cells.walkAtomPoint r.header.prepared.starParams (by decide : 0<4)
      (callPatterns r.header.call r.header.prepared
        (indexedWalk r.header.prepared.seedParameters.N r.walkCode)) (callAtoms r.header.call)) h.symm)

end NearQuarticWires.StageNativeMeaning
