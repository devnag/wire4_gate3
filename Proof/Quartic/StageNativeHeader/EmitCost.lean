import Proof.Quartic.StageNativeHeader.EmitSquare

/-!
# The emission: sizes of the fields

Paper: `lem:print`, paper/paper.tex, and `prop:time`.

The row dimension and the dense width are at most `n` (`emit_dRow_le`, `emit_width_le`), the content of the column field has
at most `3 (n+2)^2` bits (`emit_colsContent_length_le`), the cut count is at most `U = 2^d` (`emit_cuts_le_U`), and the
pieces of the marked native table request have the lengths of `pieces_length`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

theorem emit_half_mul_le (r b : ℕ) : 2 * (r / 2 * b) ≤ r * b := by
  have h : 2 * (r / 2) ≤ r := Nat.mul_div_le r 2
  calc 2 * (r / 2 * b) = 2 * (r / 2) * b := by ring
    _ ≤ r * b := Nat.mul_le_mul_right _ h

theorem emit_dRow_le (P : StarParams) : PrimT.C4Geo.dRow P ≤ P.n := by
  have h1 := P.r_mul_b_le
  have h2 := emit_half_mul_le P.r P.b
  have h3 : P.r / 2 * (P.b - P.s) ≤ P.r / 2 * P.b := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h4 := P.four_r_le_n
  have h5 := P.two_le_r
  show P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2 ≤ P.n
  omega

theorem emit_width_le (P : StarParams) : PrimT.C4Geo.width P ≤ P.n := by
  have h1 := P.r_mul_b_le
  have h2 := emit_half_mul_le P.r P.b
  have h4 := P.four_r_le_n
  have h5 := P.two_le_r
  show P.r / 2 * P.b + (P.n - P.r * P.b + 1) / 2 ≤ P.n
  omega

theorem emit_natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 :=
  NearCubicGates.Close.Cells.natWord_length v

theorem emit_nbl_le (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength
  have := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
  have := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
  omega

theorem emit_colsContent_length_le (P : StarParams) : (colsContent P).length ≤ 3 * (P.n + 2) ^ 2 := by
  have hw := emit_width_le P
  have hd := emit_dRow_le P
  unfold colsContent
  rw [List.length_append, emit_natWord_len, MatrixScorePhi.columnsWord_length]
  have hc : (PrimT.C4Geo.cols P).length = PrimT.C4Geo.dRow P := by simp [PrimT.C4Geo.cols]
  rw [hc]
  have := emit_nbl_le (PrimT.C4Geo.width P)
  have := Nat.mul_le_mul hd (show 2 * PrimT.C4Geo.width P + 1 ≤ 2 * P.n + 1 by omega)
  nlinarith

theorem emit_cuts_le_U (r : NativeHeaderRequest) : r.table.matrix.cuts.length ≤ r.table.matrix.U := r.table.cuts_le

theorem emit_U_eq (r : NativeHeaderRequest) : r.table.matrix.U = 2 ^ PrimT.C4Geo.dRow r.parameters := by
  show 2 ^ r.table.matrix.d = _; rw [r.dimension_eq]

theorem emit_q_eq (r : NativeHeaderRequest) : r.table.q = PrimT.C4Geo.dRow r.parameters + 2 * r.table.matrix.p + 3 := by
  show r.table.matrix.d + 2 * r.table.matrix.p + 3 = _; rw [r.dimension_eq]

theorem emit_count_eq (r : NativeHeaderRequest) : r.table.count = r.table.matrix.U * r.table.matrix.U := rfl

theorem emit_U_pos (r : NativeHeaderRequest) : 1 ≤ r.table.matrix.U := by rw [emit_U_eq]; exact Nat.one_le_two_pow

theorem emit_d_lt_U (r : NativeHeaderRequest) : PrimT.C4Geo.dRow r.parameters < r.table.matrix.U := by
  rw [emit_U_eq]; exact Nat.lt_two_pow_self

/-- The fixed bits after the field `q − 1`. -/
def tail7 : List Bool := [true, false, true, false, true, false, true, false, true, false, true, false, true, false]

/-- **The marked native table request, piece by piece.** -/
theorem marks_table_word (r : NativeHeaderRequest) :
    Streaming.marks r.table.word =
      (natWord (PrimT.C4Geo.dRow r.parameters)).flatMap deep3 ++ (natWord r.table.matrix.p).flatMap deep3 ++
        (natWord r.table.matrix.cuts.length).flatMap deep3 ++ (colsContent r.parameters).flatMap deep3 ++
        r.stream.flatMap deep3 ++ tailA ++ unary2 r.table.q ++ ([true, false] ++ tailA) ++
        unary2 (r.table.matrix.U * r.table.matrix.U) ++ [true, false] ++ unary2 (r.table.q - 1) ++ tail7 := by
  have h := frame_table_word r
  rw [NearCubicGates.Close.Codec.frame_eq_marks] at h
  refine List.append_cancel_right (bs := [false]) ?_
  rw [h]
  simp only [List.flatMap_append, List.append_assoc, emit_count_eq, tail7, List.cons_append, List.nil_append]

end NearQuarticWires.StageNativeHeader
