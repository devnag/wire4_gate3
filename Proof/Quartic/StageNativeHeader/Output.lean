import Proof.Quartic.StageNativeHeader.Layout

/-!
# The output of the native header printer, bit by bit

Paper: `lem:print`, paper/paper.tex.

`frame_table_word`: the framed native table request `frame (TableRequest.word)` is the header (`natWord d`,
`natWord p`, `natWord G`, the content of the column field) and the original cut bytes, each bit at depth three,
then fixed marks, the unary fields `q = d + 2p + 3`, `U²` and `q − 1` at depth two, and the empty fields.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

/-- `k` ones at depth two. -/
def unary2 (k : ℕ) : List Bool := (List.replicate k [true, true, true, true]).flatten

theorem marks_marks_replicate (k : ℕ) : marks (marks (List.replicate k true)) = unary2 k := by
  induction k with
  | zero => simp [marks, unary2]
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [unary2, List.replicate_succ, List.flatten_cons] at ih ⊢
    rw [← ih]
    simp [marks]

/-- The content of the column field. -/
def colsContent (P : StarParams) : List Bool :=
  natWord (PrimT.C4Geo.width P) ++ MatrixScorePhi.columnsWord (PrimT.C4Geo.width P) (PrimT.C4Geo.cols P)

theorem colsField_eq (P : StarParams) : PrimT.C4Geo.colsField P = frame (colsContent P) := rfl

theorem cols_eq (r : NativeHeaderRequest) : r.table.matrix.cols = PrimT.C4Geo.cols r.parameters := by
  apply List.ext_getElem
  · simp [MatrixScoreBatch.Request.cols, PrimT.C4Geo.cols, r.dimension_eq]
  · intro i hi hj
    simp only [MatrixScoreBatch.Request.cols, List.getElem_map, List.getElem_range]
    rw [r.columns_eq i, List.getD_eq_getElem _ _ hj]

/-- The header of the native table. -/
theorem header_eq (r : NativeHeaderRequest) :
    MatrixScoreBatch.header r.table.matrix = natWord (PrimT.C4Geo.dRow r.parameters) ++ natWord r.table.matrix.p ++
      natWord r.table.matrix.cuts.length ++ colsContent r.parameters := by
  unfold MatrixScoreBatch.header MatrixScoreBatch.Request.Gates colsContent
  rw [cols_eq, r.dimension_eq, r.width_eq]
  simp only [List.append_assoc]

/-- The fixed tail after the unary field `q`. -/
def tailA : List Bool := [true, true, true, false, true, false]

/-- **The framed native table request, bit by bit.** -/
theorem frame_table_word (r : NativeHeaderRequest) :
    frame r.table.word =
      (natWord (PrimT.C4Geo.dRow r.parameters) ++ natWord r.table.matrix.p ++ natWord r.table.matrix.cuts.length ++
          colsContent r.parameters ++ r.stream).flatMap deep3 ++ tailA ++ unary2 r.table.q ++ [true, false] ++
        tailA ++ unary2 r.table.count ++ [true, false] ++ unary2 (r.table.q - 1) ++ [true, false] ++
        [true, false, true, false, true, false, true, false, true, false, true, false] ++ [false] := by
  unfold TableRequest.word NearCubicWires.WireExponent3_5.CompilerMachine.Top.loadRec
    MatrixScoreBatch.physicalInput MatrixScoreBatch.word
  rw [header_eq]
  simp only [NearCubicGates.Close.Codec.frame_eq_marks, marks_append, deep3_eq, ← marks_marks_replicate,
    NativeHeaderRequest.stream]
  simp [marks, tailA, List.append_assoc]

end NearQuarticWires.StageNativeHeader
