import Proof.Quartic.StageNativeHeader.Run

/-!
# Sizes of the native header printer

Paper: `prop:time`, paper/paper.tex.

The parameters `r, b, s`, the dense width and `d` are at most `n` (`params_le`); the column field has length at most
`3 (n+2)^2` (`colsContent_length_le`); the cuts are at most the cut bytes (`cuts_le_stream`); the native table request
has length at most `24 |stream| + 4 U² + 100 (n+p+2)^2` (`tableWord_length_le`); the elementary costs are quadratic.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 x; omega

theorem pow_nbl_le' (x : ℕ) : 2 ^ natBitLength x ≤ 2 * (x + 1) :=
  NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le x

theorem natWord_len_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; have := nbl_le x; omega

/-- **The parameters are at most `n`.** -/
theorem params_le (P : StarParams) : P.r ≤ P.n ∧ P.b ≤ P.n ∧ P.s ≤ P.n ∧ PrimT.C4Geo.width P ≤ P.n ∧
    PrimT.C4Geo.dRow P ≤ P.n := by
  have h4 := P.four_r_le_n
  have hrb := P.r_mul_b_le
  have hr2 := P.two_le_r
  have hsb := s_le_b P
  have hb : P.b ≤ P.n := by nlinarith
  have hev : P.r % 2 = 0 := Nat.even_iff.mp P.r_even
  have hk : P.r * P.b = 2 * (P.r / 2 * P.b) := by
    have : P.r = 2 * (P.r / 2) := by omega
    conv_lhs => rw [this]
    ring
  have hw : PrimT.C4Geo.width P ≤ P.n := by
    unfold PrimT.C4Geo.width PrimT.C4Geo.hL; omega
  exact ⟨by omega, hb, by omega, hw, (native_dimension_le_width P).trans hw⟩

/-- The column field has quadratic length. -/
theorem colsContent_length_le (P : StarParams) : (colsContent P).length ≤ 3 * (P.n + 2) ^ 2 := by
  obtain ⟨-, -, -, hw, hd⟩ := params_le P
  have hl : (MatrixScorePhi.columnsWord (PrimT.C4Geo.width P) (PrimT.C4Geo.cols P)).length =
      PrimT.C4Geo.dRow P * (2 * PrimT.C4Geo.width P + 1) := by
    unfold MatrixScorePhi.columnsWord PrimT.C4Geo.cols
    rw [List.length_flatMap]
    simp only [List.map_map, Function.comp_def, RepairOrdinary.frame_length, SignedSortKey.binary_length,
      List.map_const', List.sum_replicate, List.length_range, smul_eq_mul]
  have hn := natWord_len_le (PrimT.C4Geo.width P)
  unfold colsContent
  rw [List.length_append, hl]
  have : PrimT.C4Geo.dRow P * (2 * PrimT.C4Geo.width P + 1) ≤ P.n * (2 * P.n + 1) :=
    Nat.mul_le_mul hd (by omega)
  nlinarith

theorem cutWord_pos (p : ℕ) (c : MatrixScoreBatch.Cut) : 1 ≤ (MatrixScoreBatch.cutWord p c).length := by
  unfold MatrixScoreBatch.cutWord MatrixScoreBatch.fields
  simp [List.length_flatMap, RepairOrdinary.frame_length]
  omega

/-- There are at most as many cuts as cut bytes. -/
theorem cuts_le_stream (r : NativeHeaderRequest) : r.table.matrix.cuts.length ≤ r.stream.length := by
  unfold NativeHeaderRequest.stream
  rw [List.length_flatMap]
  have : ∀ x ∈ r.table.matrix.cuts.map (fun c => (MatrixScoreBatch.cutWord r.table.matrix.p c).length), 1 ≤ x := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    exact cutWord_pos _ c
  have h := List.card_nsmul_le_sum _ 1 this
  simpa using h

theorem deep3_flat_length (u : List Bool) : (u.flatMap deep3).length = 8 * u.length := by
  induction u with
  | nil => simp
  | cons b u ih => simp [List.flatMap_cons, ih, deep3]; ring

theorem unary2_length (k : ℕ) : (unary2 k).length = 4 * k := by
  unfold unary2; simp [List.length_flatten]; ring

theorem one_le_count (r : NativeHeaderRequest) : 1 ≤ r.table.count := by
  unfold TableRequest.count MatrixScoreBatch.Request.U
  have := Nat.one_le_two_pow (n := r.table.matrix.d)
  nlinarith

/-- **The native table request has linear length.** -/
theorem tableWord_length_le (r : NativeHeaderRequest) :
    r.table.word.length ≤ 24 * r.stream.length + 4 * r.table.count +
      100 * (r.parameters.n + r.table.matrix.p + 2) ^ 2 := by
  have hf := congrArg List.length (frame_table_word r)
  simp only [List.length_append, deep3_flat_length, unary2_length, RepairOrdinary.frame_length, List.length_cons,
    List.length_nil, tailA] at hf
  have hd := (params_le r.parameters).2.2.2.2
  have hc := colsContent_length_le r.parameters
  have hG := cuts_le_stream r
  have h1 := natWord_len_le (PrimT.C4Geo.dRow r.parameters)
  have h2 := natWord_len_le r.table.matrix.p
  have h3 := natWord_len_le r.table.matrix.cuts.length
  have hq : r.table.q = r.table.matrix.d + 2 * r.table.matrix.p + 3 := rfl
  rw [hq, r.dimension_eq] at hf
  have hA : (r.parameters.n + 2) ^ 2 ≤ (r.parameters.n + r.table.matrix.p + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hB : 4 * (r.parameters.n + r.table.matrix.p) + 4 ≤ (r.parameters.n + r.table.matrix.p + 2) ^ 2 := by
    nlinarith
  omega

/-- The cost of reading `x` is quadratic. -/
theorem readCost_le (x : ℕ) : readCost x ≤ 200 * (x + 2) ^ 2 := by
  unfold readCost
  have h1 := nbl_le x
  have h2 := pow_nbl_le' x
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (x + 3) * (80 * x + 120) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 200 * (x + 2) ^ 2 := by nlinarith

/-- The cost of writing `x` is quadratic. -/
theorem writeCost_le (x : ℕ) : writeCost x ≤ 2000 * (x + 2) ^ 2 := by
  unfold writeCost
  have h1 := nbl_le x
  calc (natBitLength x + 10) * (100 * x + 200) ≤ (x + 11) * (100 * x + 200) := Nat.mul_le_mul (by omega) le_rfl
    _ ≤ 2000 * (x + 2) ^ 2 := by nlinarith

end NearQuarticWires.StageNativeHeader
