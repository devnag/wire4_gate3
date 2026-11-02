import Proof.Quartic.StagePullback.RowBounds
import Proof.Gates.CellsPack.Lang

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)

/-- `prop:time`, paper/paper.tex: the actual leading
dimension field reserves at most a fixed quartic binary workspace. -/
theorem row_setup_width_le (r : RowRequest) :
    rowSizes.W (leadOnes r.word) ≤ 4096 * (r.parameters.n + 1) ^ 4 := by
  have hu : 2 ^ natBitLength r.parameters.n ≤ 2 * (r.parameters.n + 1) := by
    simp only [natBitLength, pow_succ]
    have hh := Nat.pow_log_le_add_one 2 r.parameters.n
    omega
  have he : 2 ^ (4 * natBitLength r.parameters.n) = (2 ^ natBitLength r.parameters.n) ^ 4 := by
    rw [← pow_mul, Nat.mul_comm]
  simp only [rowSizes, Sz.W, r.leading_ones, he]
  calc
    _ ≤ (2 * (r.parameters.n + 1)) ^ 4 * 256 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hu 4)
    _ = _ := by ring

/-- `prop:time`, paper/paper.tex: every physical
operation of the original-source affine row machine, including setup,
source acquisition, integer arithmetic, padding, serialization and reset,
is paid by one fixed polynomial in the original dimension. -/
theorem rowCost_polynomial (r : RowRequest) :
    rowCost r ≤ 10 ^ 12 * (TSK coordinateCallee + 5000) ^ 2 * (r.parameters.n + 2) ^ 11 := by
  let V := r.parameters.n + 2
  let A := TSK coordinateCallee + 5000
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hV4 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ hV
  have hV14 : V ≤ V ^ 4 := Nat.le_self_pow (by decide) V
  have hL : leadOnes r.word ≤ V := by
    rw [r.leading_ones]
    unfold natBitLength
    have hh := Nat.log_le_self 2 r.parameters.n
    dsimp [V]
    omega
  have hL4 := hL.trans hV14
  have hW : rowSizes.W (leadOnes r.word) ≤ 4096 * V ^ 4 :=
    (row_setup_width_le r).trans (Nat.mul_le_mul_left 4096
      (Nat.pow_le_pow_left (by dsimp [V]; omega) 4))
  have hK : TSK coordinateCallee ≤ TSK coordinateCallee * V ^ 4 := by
    calc
      _ = TSK coordinateCallee * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hV4
  have hG : Gof coordinateCallee rowSizes (leadOnes r.word) ≤ A * V ^ 4 := by
    simp only [Gof, Sz.Lk, Sz.Bk, rowSizes, Nat.zero_mul, pow_zero, mul_zero, add_zero]
    change rowSizes.W (leadOnes r.word) + leadOnes r.word + 256 + 0 + 0 + 4 + 0 + 0 +
      TSK coordinateCallee + 1 ≤ A * V ^ 4
    dsimp [A]
    nlinarith only [hW, hL4, hV4, hK]
  have hV3 : 1 ≤ V ^ 3 := Nat.one_le_pow _ _ hV
  have hN : r.sourceClock + 6 + 1 ≤ 20007 * V ^ 3 := by
    have hh : r.sourceClock ≤ 20000 * V ^ 3 := r.sourceClock_cubic
    nlinarith only [hh, hV3]
  have hinput : r.word.length ≤ 10000 * V ^ 3 := r.word_length_cubic
  have hsmall : 100000 * V ^ 3 ≤ 100000 * A ^ 2 * V ^ 11 := by
    have hv : V ^ 3 ≤ V ^ 11 := Nat.pow_le_pow_right hV (by decide)
    have ha : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
    have hh : V ^ 3 ≤ A ^ 2 * V ^ 11 := hv.trans (Nat.le_mul_of_pos_left _ ha)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 100000 hh
  have h := NearCubicGates.Close.CellsPack.lang_le2 coordinateCallee rowSizes r.word (r.sourceClock + 6)
  change rowCost r ≤ 10 ^ 12 * A ^ 2 * V ^ 11
  calc
    rowCost r ≤ 10 ^ 6 * ((r.sourceClock + 6 + 1) *
        Gof coordinateCallee rowSizes (leadOnes r.word) ^ 2) + 10 * r.word.length := h
    _ ≤ 10 ^ 6 * ((20007 * V ^ 3) * (A * V ^ 4) ^ 2) + 100000 * V ^ 3 := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2))
      · calc
          10 * r.word.length ≤ 10 * (10000 * V ^ 3) := Nat.mul_le_mul_left 10 hinput
          _ = _ := by ring
    _ ≤ 10 ^ 12 * A ^ 2 * V ^ 11 := by
      have he : 10 ^ 6 * ((20007 * V ^ 3) * (A * V ^ 4) ^ 2) =
          20007000000 * A ^ 2 * V ^ 11 := by ring
      rw [he]
      calc
        _ ≤ 20007000000 * A ^ 2 * V ^ 11 + 100000 * A ^ 2 * V ^ 11 :=
          Nat.add_le_add_left hsmall _
        _ = 20007100000 * (A ^ 2 * V ^ 11) := by ring
        _ ≤ 10 ^ 12 * (A ^ 2 * V ^ 11) := Nat.mul_le_mul_right _ (by decide)
        _ = _ := by ring

end NearQuarticWires.StagePullback
