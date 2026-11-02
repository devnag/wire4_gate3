import Proof.Quartic.Cells.ParametersPreparationLoopCost
import Proof.Quartic.Cells.ParametersPublicFixedBits

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: a fixed coefficient for the actual nine-block early
public computation, including its integer loops and rational reductions. -/
def publicScalesCostCoefficient (B1 : ℕ) : ℕ :=
  let A := preparationCoefficient B1 + 33 * B1 + 4000
  300 + 100000 + (5 * (B1 + 20) + 100) + (20 * (B1 + 20000) ^ 2 + 20000) +
    (28 * A + 128) + (2880 * (B1 + 20) ^ 2 + 158) + 50000 +
    (42 * A + 148) + (30 * (2 * B1 + 112) + 20100) + 8

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: the exact executed public-scale cost has one fixed
polynomial upper bound in the original serialized input length. -/
theorem publicScalesCost_preparation_bound (hs : CoreRules x p) (B1 L num den : ℕ)
    (hn : x.n ≤ L) (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num = num) (hden : x.beta.den = den)
    (hu : 0 < num) (hd : 0 < den)
    (hnumBits : num ≤ 2 ^ L) (hdenBits : den ≤ 2 ^ L) :
    StagePrep.publicScalesCost x p num den ≤
      publicScalesCostCoefficient B1 * (L + 1) ^ (2 * B1 + 12) := by
  let R := (L + 1) ^ (2 * B1 + 12)
  let H := preparationBitBase B1 L
  let A := preparationCoefficient B1 + 33 * B1 + 4000
  have hR : 1 ≤ R := Nat.pow_pos (Nat.succ_pos L)
  have hLP (d : ℕ) (hd : d ≤ 2 * B1 + 12) : (L + 1) ^ d ≤ R :=
    Nat.pow_le_pow_right (Nat.succ_pos L) hd
  have hNP (d : ℕ) (hd : d ≤ 2 * B1 + 12) : x.n ^ d ≤ R :=
    (Nat.pow_le_pow_left (hn.trans (Nat.le_succ L)) d).trans (hLP d hd)
  have hN1P (d : ℕ) (hd : d ≤ 2 * B1 + 12) : (x.n + 1) ^ d ≤ R :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) d).trans (hLP d hd)
  have hHR : H ≤ A * R := (preparationBitBase_cubic B1 L).trans
    (Nat.mul_le_mul_left _ (hLP 3 (by omega)))
  have h1 : 10 * x.n * (x.n + 1) + 15 * x.n + 251 ≤ 300 * R := by
    have hp : 10 * x.n * (x.n + 1) + 15 * x.n + 251 ≤ 300 * (L + 1) ^ 2 := by
      have hn2 := Nat.pow_le_pow_left hn 2
      nlinarith only [hn, hn2, Nat.zero_le L]
    exact hp.trans (Nat.mul_le_mul_left _ (hLP 2 (by omega)))
  have h2 : StagePrep.concentrationCost p.m p.k p.Jmax x.beta ≤ 100000 * R :=
    (hs.concentrationCost_preparation_bound L hn (by rwa [hden])).trans
      (Nat.mul_le_mul_left _ (hLP 4 (by omega)))
  have htau : p.tau ≤ (B1 + 20) * R := (hs.tau_preparation_bound B1 hb).trans
    (Nat.mul_le_mul_left _ (hNP 2 (by omega)))
  have h3 : StagePrep.tauCost x.beta ≤ (5 * (B1 + 20) + 100) * R := by
    have hc : ParameterArithmetic.ceilLog 2 (16 / x.beta) ≤ p.tau := by rw [hs.tau_eq]; omega
    unfold StagePrep.tauCost
    nlinarith only [hc, htau, hR]
  have h4 : 20 * StagePrep.uRootArgument x.n p.r x.W num den + 20000 ≤
      (20 * (B1 + 20000) ^ 2 + 20000) * R :=
    (hs.uProgram_budget_preparation_bound B1 num den hb hnum hden hu hd).trans
      (Nat.mul_le_mul_left _ (hN1P (2 * B1 + 8) (by omega)))
  have hscalar := hs.early_preparation_bounds B1 hb
  have hV := hs.preparationEnvelope_binary_height B1 L hn
  have hτB : p.tau < 2 ^ (H + 1) := (hscalar.tau.trans hV).trans_lt
    (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hUB : 4 * p.U < 2 ^ (H + 1) := (hscalar.pi0_denominator.trans hV).trans_lt
    (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hsτ : Nat.size p.tau ≤ H + 1 := Nat.size_le.mpr hτB
  have hsU : Nat.size (4 * p.U) ≤ H + 1 := Nat.size_le.mpr hUB
  have h5 : 14 * (Nat.size p.tau + Nat.size (4 * p.U)) + 100 ≤ (28 * A + 128) * R := by
    nlinarith only [hsτ, hsU, hHR, hR]
  have hxarg : StagePrep.xMaxArgument x.n p.r p.tau ≤ 144 * (B1 + 20) ^ 2 * x.n ^ 6 := by
    simpa only [StagePrep.xMaxArgument, pow_two] using hs.Xmax_radicand_preparation_bound B1 hb
  have h6 : 20 * StagePrep.xMaxArgument x.n p.r p.tau + 158 ≤
      (2880 * (B1 + 20) ^ 2 + 158) * R := by
    have h := hxarg.trans (Nat.mul_le_mul_left _ (hNP 6 (by omega)))
    nlinarith only [h, hR]
  have htheta : StagePrep.fourierTheta p.m x.G1 x.G2 ≤ 2178 * x.n ^ 8 := by
    have heq : StagePrep.fourierTheta p.m x.G1 x.G2 = p.omega1 * p.omega2 := by
      rw [hs.omega1_eq, hs.omega2_eq]
      rfl
    rw [heq]
    have h := hs.theta_preparation_bound
    omega
  have h7 : 20 * StagePrep.fourierTheta p.m x.G1 x.G2 + 160 ≤ 50000 * R := by
    have h := htheta.trans (Nat.mul_le_mul_left _ (hNP 8 (by omega)))
    nlinarith only [h, hR]
  have hnumH : Nat.size num ≤ H + 1 := by
    apply Nat.size_le.mpr
    exact hnumBits.trans_lt (Nat.pow_lt_pow_right (by norm_num)
      (by have := (preparationBitBase_bounds B1 L).2.1; omega))
  have hMF : 16 * p.MF ≤ 2 ^ H := (hs.early_operand_binary_bounds B1 L hn hb).2.2.2.2.2.2.2
  have hL : L ≤ H := (preparationBitBase_bounds B1 L).2.1
  have hdenH : den ≤ 2 ^ H := hdenBits.trans (Nat.pow_le_pow_right (by norm_num) hL)
  have hprod : 16 * p.MF * den < 2 ^ (2 * H + 1) := by
    calc
      _ ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hMF hdenH
      _ = 2 ^ (2 * H) := by rw [← pow_add]; exact congrArg (fun e : ℕ => 2 ^ e) (by omega)
      _ < _ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hprodsize : Nat.size (16 * p.MF * den) ≤ 2 * H + 1 := Nat.size_le.mpr hprod
  have h8 : 14 * (Nat.size num + Nat.size (16 * p.MF * den)) + 120 ≤ (42 * A + 148) * R := by
    nlinarith only [hnumH, hprodsize, hHR, hR]
  have hq : p.Qexp ≤ (2 * B1 + 112) * R := (hs.Qexp_preparation_bound B1 hb).trans
    (Nat.mul_le_mul_left _ (hNP 2 (by omega)))
  have h9 : 30 * p.Qexp + 20100 ≤ (30 * (2 * B1 + 112) + 20100) * R := by
    nlinarith only [hq, hR]
  have hlast : 8 ≤ 8 * R := by omega
  calc
    StagePrep.publicScalesCost x p num den ≤ 300 * R + 100000 * R +
        (5 * (B1 + 20) + 100) * R + (20 * (B1 + 20000) ^ 2 + 20000) * R +
        (28 * A + 128) * R + (2880 * (B1 + 20) ^ 2 + 158) * R + 50000 * R +
        (42 * A + 148) * R + (30 * (2 * B1 + 112) + 20100) * R + 8 * R := by
      unfold StagePrep.publicScalesCost
      omega
    _ = _ := by unfold publicScalesCostCoefficient; dsimp [A, R]; ring

end NearQuarticWires.Cells.CoreRules
