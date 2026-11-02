import Proof.Quartic.Cells.ParametersPreparationWords

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- Scalar-value bounds for the parameter record of `sec:params`,
paper/paper.tex: the cell side fits the public arity. -/
theorem b_preparation_bound (hs : CoreRules x p) : p.b ≤ x.n := by
  have hn : x.n / p.r + 1 ≠ 0 := Nat.succ_ne_zero _
  have hp := Nat.pow_log_le_self 2 hn
  rw [hs.b_eq, hs.s_eq]
  have hpred : 2 ^ Nat.log 2 (x.n / p.r + 1) - 1 ≤ x.n / p.r := by
    simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hp 1
  exact hpred.trans (Nat.div_le_self _ _)

/-- `sec:params` and `prop:time`, paper/paper.tex: the inner dimension has a uniform quadratic value bound. -/
theorem k_preparation_bound (hs : CoreRules x p) : p.k ≤ 16 * x.n ^ 2 := by
  have hL := hs.lambda_le_n
  have hM := hs.mu_le_lambda.trans hL
  have hprod := Nat.mul_le_mul hM hL
  nlinarith only [hs.k_le, hprod]

/-- `sec:params` and `prop:time`, paper/paper.tex: the concentration field has a quadratic value bound. -/
theorem T_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : p.T ≤ (B1 + 80) * x.n ^ 2 := by
  have hL := hs.lambda_le_n
  have hM := hs.mu_le_lambda.trans hL
  calc
    p.T ≤ (B1 + 80) * p.mu * p.lambda := hs.T_upper B1 hb
    _ ≤ (B1 + 80) * x.n * x.n := by gcongr
    _ = _ := by ring

/-- `sec:params` and `prop:time`, paper/paper.tex: a polynomial value bound for the exact integer root. -/
theorem Xmax_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : p.Xmax ≤ 48 * (B1 + 20) * x.n ^ 4 := by
  have hroot : p.Xmax ≤ 3 * p.tau * x.n * p.r := by
    apply (hs.Xmax_le_iff _).mpr
    have hNR : x.n * p.r ≤ (x.n * p.r) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h := Nat.mul_le_mul_left (9 * p.tau ^ 2) hNR
    nlinarith only [h]
  have hM := hs.mu_le_lambda.trans hs.lambda_le_n
  have hr : p.r ≤ 16 * x.n := by rw [hs.r_eq]; exact Nat.mul_le_mul_left _ hM
  calc
    p.Xmax ≤ 3 * p.tau * x.n * p.r := hroot
    _ ≤ 3 * ((B1 + 20) * x.n ^ 2) * x.n * (16 * x.n) := by
      gcongr
      exact hs.tau_preparation_bound B1 hb
    _ = _ := by ring

/-- `sec:params` and `prop:time`, paper/paper.tex: the selected heavy-incidence threshold has polynomial value. -/
theorem dstar_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.dstar ≤ (96 * (B1 + 20) * (B1 + 20000)) * x.n ^ (B1 + 8) := by
  calc
    p.dstar ≤ 2 * p.Xmax * p.U := by rw [hs.dstar_eq]; exact Nat.div_le_self _ _
    _ ≤ 2 * (48 * (B1 + 20) * x.n ^ 4) * ((B1 + 20000) * x.n ^ (B1 + 4)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (hs.Xmax_preparation_bound B1 hb))
        (hs.U_preparation_bound B1 hb)
    _ = _ := by simp only [pow_add]; ring

/-- `sec:params` and `prop:time`, paper/paper.tex: the sample-size exponent has a quadratic value bound. -/
theorem Qexp_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : p.Qexp ≤ (2 * B1 + 112) * x.n ^ 2 := by
  have hq := hs.Qexp_four_upper B1 hb
  have hk := hs.k_preparation_bound
  have hL := hs.lambda_le_n
  have hn : x.n ≤ x.n ^ 2 := Nat.le_self_pow (by norm_num) _
  have hm := Nat.mul_le_mul_left (2 * B1 + 100) (hL.trans hn)
  nlinarith only [hq, hk, hm]

/-- `sec:params` and `prop:time`, paper/paper.tex: the field degree and full seed length have quadratic value. -/
theorem seed_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.ellf ≤ (2 * B1 + 130) * (x.n + 1) ^ 2 ∧
      p.S ≤ (8 * (2 * B1 + 130)) * (x.n + 1) ^ 2 := by
  have hk := hs.k_preparation_bound
  have hq := hs.Qexp_preparation_bound B1 hb
  have he : p.ellf ≤ (2 * B1 + 130) * (x.n + 1) ^ 2 := by
    rw [hs.ellf_eq]
    apply max_le <;> nlinarith only [hk, hq, Nat.zero_le B1, Nat.zero_le x.n]
  refine ⟨he, ?_⟩
  rw [hs.S_eq, hs.m_eq]
  have h := Nat.mul_le_mul_left 8 he
  nlinarith only [h]

/-- `sec:params` and `prop:time`, paper/paper.tex: the signed numerator exponent has quadratic value. -/
theorem BN_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : p.BN ≤ (32 * B1 + 2200) * x.n ^ 2 := by
  have hL := hs.lambda_le_n
  have hM := hs.mu_le_lambda.trans hL
  calc
    p.BN ≤ (32 * B1 + 2200) * p.mu * p.lambda := hs.BN_upper B1 hb
    _ ≤ (32 * B1 + 2200) * x.n * x.n := by gcongr
    _ = _ := by ring

end NearQuarticWires.Cells.CoreRules
