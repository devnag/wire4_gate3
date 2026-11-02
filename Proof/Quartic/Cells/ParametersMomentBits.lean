import Proof.Quartic.Cells.ParametersEncodingEnvelope

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- A common binary height for the signed certification moments,
`eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex. -/
def certificateBitEnvelope (V : ℕ) : ℕ := 100 * (V + 1) ^ 2

/-- The Newton mask remains bounded before certification, including
bad columns, `lem:maskpoly`, paper/paper.tex. -/
theorem certificate_mask_power_bound (V Xmax G : ℕ) (hX : Xmax ≤ V) (hG : G ≤ V) :
    (Xmax + 1) * 2 ^ (Xmax + G) ≤ 2 ^ (3 * V + 1) := by
  calc
    (Xmax + 1) * 2 ^ (Xmax + G) ≤ 2 ^ (V + 1) * 2 ^ (2 * V) :=
      Nat.mul_le_mul ((Nat.add_le_add_right hX 1).trans Nat.lt_two_pow_self.le)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 2 ^ (3 * V + 1) := by rw [← pow_add]; congr 1; omega

/-- The residual envelope allows exponentially valued chain
parameters of polynomial bit height, `eq:testE`–`eq:testPhi`,
paper/paper.tex. -/
theorem certificate_residual_power_bound (V G rate M A : ℕ) (hG : G ≤ V)
    (hr : rate ≤ 2 ^ V) (hM : M ≤ 2 ^ V) (hA : A ≤ 2 ^ V) :
    8 * G * (1 + rate + M + A) ≤ 2 ^ (2 * V + 6) := by
  have hsum : 1 + rate + M + A ≤ 4 * 2 ^ V := by
    have hone := @Nat.one_le_two_pow V
    omega
  calc
    8 * G * (1 + rate + M + A) ≤ 8 * 2 ^ V * (4 * 2 ^ V) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (hG.trans Nat.lt_two_pow_self.le)) hsum
    _ = 2 ^ (V + V + 5) := by simp only [pow_add]; norm_num; ring
    _ ≤ 2 ^ (2 * V + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The full eighth-order signed walk moment, including its
structural mask and all walks, fits a polynomial binary height
without assuming certification, `eq:testE`–`eq:testPhi`,
paper/paper.tex. -/
theorem certificate_walk_moment_power_bound (V k N Xmax G rate M A : ℕ)
    (hk : k ≤ V) (hN : N = 2 ^ (k / 2)) (hX : Xmax ≤ V) (hG : G ≤ V)
    (hr : rate ≤ 2 ^ V) (hM : M ≤ 2 ^ V) (hA : A ≤ 2 ^ V) :
    N ^ 8 * ((Xmax + 1) * 2 ^ (Xmax + G)) ^ 8 *
        (8 * G * (1 + rate + M + A)) ^ (8 * k) ≤ 2 ^ certificateBitEnvelope V := by
  have hn : N ≤ 2 ^ V := by
    rw [hN]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.div_le_self k 2).trans hk)
  have hmask := certificate_mask_power_bound V Xmax G hX hG
  have hres := certificate_residual_power_bound V G rate M A hG hr hM hA
  calc
    N ^ 8 * ((Xmax + 1) * 2 ^ (Xmax + G)) ^ 8 *
        (8 * G * (1 + rate + M + A)) ^ (8 * k) ≤
        (2 ^ V) ^ 8 * (2 ^ (3 * V + 1)) ^ 8 * (2 ^ (2 * V + 6)) ^ (8 * k) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hn _) (Nat.pow_le_pow_left hmask _))
        (Nat.pow_le_pow_left hres _)
    _ = 2 ^ (V * 8 + (3 * V + 1) * 8 + (2 * V + 6) * (8 * k)) := by
      simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ certificateBitEnvelope V := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hprod := Nat.mul_le_mul_left (2 * V + 6) (Nat.mul_le_mul_left 8 hk)
      unfold certificateBitEnvelope
      nlinarith only [hprod, Nat.zero_le V]

/-- The population moment also fits the same binary height before
certification, `eq:testX`, paper/paper.tex. -/
theorem certificate_population_power_bound (V k N G : ℕ)
    (hk : k ≤ V) (hN : N = 2 ^ (k / 2)) (hG : G ≤ V) :
    N ^ 2 * G ^ (2 * k) ≤ 2 ^ certificateBitEnvelope V := by
  have hn : N ≤ 2 ^ V := by
    rw [hN]
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.div_le_self k 2).trans hk)
  calc
    N ^ 2 * G ^ (2 * k) ≤ (2 ^ V) ^ 2 * (2 ^ V) ^ (2 * k) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hn _) (Nat.pow_le_pow_left (hG.trans Nat.lt_two_pow_self.le) _)
    _ = 2 ^ (V * 2 + V * (2 * k)) := by simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ certificateBitEnvelope V := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hprod := Nat.mul_le_mul_left V (Nat.mul_le_mul_left 2 hk)
      unfold certificateBitEnvelope
      nlinarith only [hprod, Nat.zero_le V]

/-- Every literal natural threshold in the three moment tests fits
the same binary height, `eq:testX`–`eq:testPhi`, paper/paper.tex. -/
theorem certificate_threshold_power_bound (V k b d : ℕ)
    (hk : k ≤ V) (hb : b ≤ 2 ^ (V + 1)) (hd : d ≤ 8 * k) :
    b ^ d ≤ 2 ^ certificateBitEnvelope V := by
  calc
    b ^ d ≤ (2 ^ (V + 1)) ^ d := Nat.pow_le_pow_left hb _
    _ = 2 ^ ((V + 1) * d) := (pow_mul ..).symm
    _ ≤ 2 ^ certificateBitEnvelope V := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hprod := Nat.mul_le_mul_left (V + 1) (hd.trans (Nat.mul_le_mul_left 8 hk))
      unfold certificateBitEnvelope
      nlinarith only [hprod, Nat.zero_le V]

end NearQuarticWires.Cells.ParameterArithmetic
