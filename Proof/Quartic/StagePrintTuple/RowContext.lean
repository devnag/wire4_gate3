import Proof.Quartic.StagePrint.HeaderSource
import Proof.Quartic.StagePrint.OriginalNativeRow
import Proof.Quartic.StagePrint.RoleSemantics
import Proof.Quartic.StagePrint.CallEquationTables

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: the actual original call, canonical walk and
proof-only original bit bounds determine every native child row. -/
structure RowContext where
  header : StagePrint.Header.HeaderCall
  walkCode : Fin (header.prepared.seedParameters.N ^ 8)
  gate_bits : ∀ i : Fin (Builder.allGates header.call).length,
    GateBits (Call.B0 header.call.n) (StagePrint.callAtoms header.call i)

/-- `lem:print`, paper/paper.tex:
the formula atom selects one original occurrence, with duplicate gates
remaining distinct finite-list positions. -/
def RowContext.originalIndex (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    Fin (Builder.allGates r.header.call).length := (finProdFinEquiv.symm i).2

/-- `lem:print`, paper/paper.tex:
the same atom selects exactly one of the original seventeen star roles. -/
def RowContext.role (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) : Cells.OffsetRole 4 :=
  (Cells.offsetIndex 4).symm (finProdFinEquiv.symm i).1

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: one original exact child is placed at the actual
translated canonical walk role before the same-phi native row pullback. -/
def RowContext.originalRow (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    StagePrint.OriginalRowData where
  parameters := Builder.star r.header.call r.header.prepared
  gate := StagePrint.callAtoms r.header.call (r.originalIndex i)
  gate_bits := r.gate_bits (r.originalIndex i)
  index := j
  translation := Builder.translation r.header.call r.header.prepared r.header.witness
  left := finCongr (Builder.seedN_eq_patternCodes r.header.call r.header.prepared)
    (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
      (StagePrint.Header.roleLeftSlot (r.role i)))
  right := finCongr (Builder.seedN_eq_patternCodes r.header.call r.header.prepared)
    (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
      (StagePrint.Header.roleRightSlot (r.role i)))
  useLeft := StagePrint.Header.leftCornerCode (finProdFinEquiv.symm i).1.val
  useRight := StagePrint.Header.rightCornerCode (finProdFinEquiv.symm i).1.val
  transpose := true

/-- `lem:print`, paper/paper.tex: the analytic
native child pool follows the original exact-child order and carries
all signed dense affine weights and the target as its last field. -/
def RowContext.nativeKids (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) : List (List ℤ) :=
  List.ofFn fun j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length =>
    List.ofFn (r.originalRow i j).nativeChild.weight ++ [(r.originalRow i j).nativeChild.target]

/-- `lem:print`, paper/paper.tex: row pullback
never changes the number of ORIGINAL exact children. -/
theorem RowContext.nativeKids_length (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    (r.nativeKids i).length = (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length := by
  simp only [RowContext.nativeKids, List.length_ofFn]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every native row has the same two-half coordinate count
and one final signed target field. -/
theorem RowContext.nativeKids_row_length (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) :
    ∀ row ∈ r.nativeKids i, row.length =
      2 * NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.header.prepared.starParams + 1 := by
  intro row hrow
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
  simp [RowContext.originalRow, StagePrint.OriginalRowData.nativeChild, Builder.star]
  omega

/-- `imp:disjoint`, `lem:print` and `prop:time`, paper/paper.tex: the native pool obeys the unchanged
sharp original-child cap, independently of affine or stacking widths. -/
theorem RowContext.nativeKids_length_le (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length)) (hn : 0 < r.header.call.n) :
    (r.nativeKids i).length ≤ Cells.childCap r.header.call.n (Call.B0 r.header.call.n) := by
  rw [r.nativeKids_length]
  exact Cells.exactChildren_length_childCap hn _ _ (r.gate_bits (r.originalIndex i))

end NearQuarticWires.StageTuple
