import Proof.Quartic.Cells.ParametersPreparationBits

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: the initial parsed header computation fits a cubic
binary width on both outcomes of the initial geometry test. -/
theorem preparationHeader_operand_binary_bound (B1 L n w1 w2 : ℕ)
    (hn : n ≤ L) (hw1 : w1 ≤ 2 ^ L) (hw2 : w2 ≤ 2 ^ L) :
    (3 * n + 4) * (n + 1) + w1 + w2 + 100 * n + 100 <
      2 ^ (100 * preparationBitBase B1 L) := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hnB : n ≤ 2 ^ H := (hn.trans hH.2.1).trans Nat.lt_two_pow_self.le
  have hw1B : w1 ≤ 2 ^ H := hw1.trans (Nat.pow_le_pow_right (by norm_num) hH.2.1)
  have hw2B : w2 ≤ 2 ^ H := hw2.trans (Nat.pow_le_pow_right (by norm_num) hH.2.1)
  have hn2 := Nat.pow_le_pow_left hnB 2
  have hZ : 1 ≤ (2 : ℕ) ^ H := Nat.one_le_two_pow
  have hZ2 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hsmall : (3 * n + 4) * (n + 1) + w1 + w2 + 100 * n + 100 <
      256 * ((2 : ℕ) ^ H) ^ 2 := by
    nlinarith only [hnB, hw1B, hw2B, hn2, hZ, hZ2]
  have heq : 256 * ((2 : ℕ) ^ H) ^ 2 = 2 ^ (2 * H + 8) := by
    rw [show 2 * H + 8 = H * 2 + 8 by omega, pow_add, pow_mul]
    norm_num
    ring
  rw [heq] at hsmall
  exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

end NearQuarticWires.Cells.ParameterArithmetic
