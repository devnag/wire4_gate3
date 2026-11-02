import Proof.Quartic.StagePrintTuple.RowContext
import Proof.Quartic.StagePrint.BaseHeaderEmit

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: every original
row uses the same actual affine input bit width, independently of the
occurrence, child, walk role or signed coefficient. -/
def RowContext.inputFieldWidth (r : RowContext) : ℕ :=
  (4 * r.header.call.n + 1) * Nat.clog 2 (r.header.call.n + 1) + 5

/-- `lem:print`, paper/paper.tex: the actual row
printer's common output width includes the original field and all
possible affine target shifts. -/
def RowContext.nativeFieldWidth (r : RowContext) : ℕ :=
  r.inputFieldWidth + r.header.call.n + 6

/-- `lem:print`, paper/paper.tex: the row caller's
literal original input width equals the paid common header field. -/
theorem RowContext.originalRow_Lin_eq (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.originalRow i j).canonicalPullback.Lin = r.inputFieldWidth := by
  change (Call.B0 r.header.call.n + Nat.clog 2 (r.header.call.n + 1) + 4) + 1 = _
  unfold RowContext.inputFieldWidth Call.B0
  ring

/-- `lem:print`, paper/paper.tex: the real row
machine's output width is exactly the common actual third header field. -/
theorem RowContext.originalRow_Lout_eq (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.originalRow i j).canonicalPullback.Lout = r.nativeFieldWidth := by
  unfold StagePullback.RowRequest.Lout RowContext.nativeFieldWidth
  rw [r.originalRow_Lin_eq]
  rfl

/-- `lem:print`, paper/paper.tex: the actual raw
row output has this common native field width before any paid stacking
width extension; no row-value input or output-length oracle occurs. -/
theorem RowContext.originalRow_output (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.originalRow i j).canonicalPullback.output = fieldsRecs r.nativeFieldWidth
      [List.ofFn (r.originalRow i j).nativeChild.weight ++ [(r.originalRow i j).nativeChild.target]] := by
  rw [StagePrint.OriginalRowData.native_output, r.originalRow_Lout_eq]

/-- `lem:print`, paper/paper.tex: the common
native output width is the exact value already carried by the actual
first-seven-header source, with no extra runtime field. -/
theorem RowContext.baseHeader_nativeWidth (r : RowContext) :
    (StagePrint.Header.baseHeaderValues r.header)[2]? = some r.nativeFieldWidth := by
  simp only [StagePrint.Header.baseHeaderValues, List.getElem?_cons_succ, List.getElem?_cons_zero]
  rfl

end NearQuarticWires.StageTuple
