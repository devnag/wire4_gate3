import Proof.Quartic.Cells.ParametersPreparationTailBits
import Proof.Quartic.StagePrep.PublicScalesProgram

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: the fixed arithmetic guards in the early public
execution, with the root and rational products stated literally. -/
structure PublicFixedOperandBounds (H : ℕ) (x : ParameterInput) (p : Parameters)
    (num den : ℕ) : Prop where
  dimensions : x.n * (x.n + 1) + 2 * x.n + 32 ≤ 100 * H
  tau : p.k + 32 * den + 4 * num + 16 < 2 ^ (100 * H)
  pi : 2 * (p.tau + 4 * p.U) + 4 < 2 ^ (100 * H)
  populationRoot : StagePrep.xMaxArgument x.n p.r p.tau * StagePrep.xMaxArgument x.n p.r p.tau +
    StagePrep.xMaxArgument x.n p.r p.tau + 3 < 2 ^ (100 * H)
  populationCut : 2 * p.Xmax * p.U + 6 * p.r * p.tau + 16 < 2 ^ (100 * H)
  fourier : StagePrep.fourierTheta p.m x.G1 x.G2 * StagePrep.fourierTheta p.m x.G1 x.G2 +
    StagePrep.fourierTheta p.m x.G1 x.G2 + 4 * p.m + 16 < 2 ^ (100 * H)
  eta : 2 * (num + 16 * p.MF * den) + 4 < 2 ^ (100 * H)
  exponent : p.Qexp < 100 * H
  seed : 2 * p.m * max p.k (p.Qexp + 1) + p.k + p.Qexp + 32 < 2 ^ (100 * H)

namespace CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: all remaining fixed guards of the exact early
public program fit a common cubic original-input bit scale. -/
theorem publicScales_fixed_operand_binary_bounds (hs : CoreRules x p) (B1 L num den : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : num ≤ 2 ^ L) (hden : den ≤ 2 ^ L) :
    PublicFixedOperandBounds (preparationBitBase B1 L) x p num den := by
  generalize hHdef : preparationBitBase B1 L = H
  have hH := preparationBitBase_bounds B1 L
  rw [hHdef] at hH
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  rw [hHdef] at hV
  have hsval := hs.early_preparation_bounds B1 hb
  have he := hs.early_operand_binary_bounds B1 L hn hb
  simp only [hHdef] at he
  have hnB : x.n ≤ 2 ^ H := he.1
  have hr : p.r ≤ 2 ^ H := he.2.1
  have hU : p.U ≤ 2 ^ H := he.2.2.2.2.1
  have htau : p.tau ≤ 2 ^ H := hsval.tau.trans hV
  have hk : p.k ≤ 2 ^ H := hsval.k.trans hV
  have hX : p.Xmax ≤ 2 ^ H := hsval.Xmax.trans hV
  have hMF : 16 * p.MF ≤ 2 ^ H := he.2.2.2.2.2.2.2
  have hQexp : p.Qexp ≤ 2 ^ H := hsval.Qexp.trans hV
  have hS : p.S ≤ 2 ^ H := hsval.S.trans hV
  have hnumB : num ≤ 2 ^ H := hnum.trans (Nat.pow_le_pow_right (by norm_num) hH.2.1)
  have hdenB : den ≤ 2 ^ H := hden.trans (Nat.pow_le_pow_right (by norm_num) hH.2.1)
  have hZ : 1024 ≤ (2 : ℕ) ^ H := (by norm_num : 1024 ≤ 2 ^ 10).trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hZ2 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hZ4 : 2 ^ H ≤ ((2 : ℕ) ^ H) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hpromote (a c d : ℕ) (ha : a < c * ((2 : ℕ) ^ H) ^ d)
      (hc : c ≤ 64) (hd : d ≤ 4) : a < 2 ^ (100 * H) := by
    have hp : (2 : ℕ) ^ H ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc' : c ≤ 2 ^ 6 := by norm_num; exact hc
    calc
      a < c * ((2 : ℕ) ^ H) ^ d := ha
      _ ≤ 2 ^ 6 * ((2 : ℕ) ^ H) ^ 4 := Nat.mul_le_mul hc'
        (Nat.pow_le_pow_right (by omega) hd)
      _ = 2 ^ (6 + H * 4) := by rw [← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hroot : StagePrep.xMaxArgument x.n p.r p.tau ≤ ((2 : ℕ) ^ H) ^ 2 := by
    have hc := ((hs.Xmax_le_iff p.Xmax).mp le_rfl)
    have heq : StagePrep.xMaxArgument x.n p.r p.tau = 9 * p.tau ^ 2 * x.n * p.r := by
      unfold StagePrep.xMaxArgument
      ring
    rw [heq]
    exact hc.trans (Nat.pow_le_pow_left hX 2)
  have hrootSq := Nat.mul_le_mul hroot hroot
  have htheta : StagePrep.fourierTheta p.m x.G1 x.G2 ≤ ((2 : ℕ) ^ H) ^ 2 := by
    have ht : StagePrep.fourierTheta p.m x.G1 x.G2 = p.omega1 * p.omega2 := by
      rw [hs.omega1_eq, hs.omega2_eq]
      rfl
    rw [ht]
    simpa only [pow_two] using Nat.mul_le_mul he.2.2.2.2.2.1 he.2.2.2.2.2.2.1
  have hthetaSq := Nat.mul_le_mul htheta htheta
  have hXU : p.Xmax * p.U ≤ ((2 : ℕ) ^ H) ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hX hU
  have hrt : p.r * p.tau ≤ ((2 : ℕ) ^ H) ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hr htau
  have hMFden : 16 * p.MF * den ≤ ((2 : ℕ) ^ H) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hMF hdenB
  refine {
    dimensions := ?_
    tau := hpromote _ 64 1 (by simp only [pow_one]; omega) (by norm_num) (by norm_num)
    pi := hpromote _ 16 1 (by simp only [pow_one]; omega) (by norm_num) (by norm_num)
    populationRoot := hpromote _ 4 4 ?_ (by norm_num) (by norm_num)
    populationCut := hpromote _ 32 2 (by nlinarith only [hXU, hrt, hZ, hZ2]) (by norm_num) (by norm_num)
    fourier := hpromote _ 4 4 ?_ (by norm_num) (by norm_num)
    eta := hpromote _ 16 2 (by nlinarith only [hMFden, hnumB, hZ, hZ2]) (by norm_num) (by norm_num)
    exponent := ?_
    seed := ?_ }
  · have hn2 := Nat.pow_le_pow_left hn 2
    have hquad : 100 * (L + 1) ^ 2 ≤ H := by rw [← hHdef]; unfold preparationBitBase; omega
    nlinarith only [hn, hn2, hquad, Nat.zero_le L]
  · have hpow24 : ((2 : ℕ) ^ H) ^ 2 ≤ ((2 : ℕ) ^ H) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith only [hroot, hrootSq, hZ, hZ4, hpow24]
  · have hpow24 : ((2 : ℕ) ^ H) ^ 2 ≤ ((2 : ℕ) ^ H) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    rw [hs.m_eq]
    rw [hs.m_eq] at htheta hthetaSq
    nlinarith only [htheta, hthetaSq, hZ, hZ4, hpow24]
  · have hq := hs.Qexp_preparation_bound B1 hb
    have hpow : x.n ^ 2 ≤ (L + 1) ^ 3 :=
      (Nat.pow_le_pow_left (hn.trans (Nat.le_succ L)) 2).trans
        (Nat.pow_le_pow_right (Nat.succ_pos L) (by omega))
    have hqH : p.Qexp ≤ H := by
      calc
        p.Qexp ≤ (2 * B1 + 112) * x.n ^ 2 := hq
        _ ≤ (32 * B1 + 2200) * (L + 1) ^ 3 := Nat.mul_le_mul (by omega) hpow
        _ ≤ H := by rw [← hHdef]; unfold preparationBitBase; omega
    omega
  · have hseed : 2 * p.m * max p.k (p.Qexp + 1) = p.S := by rw [hs.S_eq, hs.ellf_eq]
    rw [hseed]
    exact hpromote _ 64 1 (by simp only [pow_one]; omega) (by norm_num) (by norm_num)

end CoreRules

end NearQuarticWires.Cells
