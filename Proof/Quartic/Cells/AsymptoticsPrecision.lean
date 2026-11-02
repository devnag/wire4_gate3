import Proof.Quartic.Cells.AsymptoticsGeometry

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: polynomial
precision gives a denominator-independent upper bound for its binary logarithm. -/
theorem precision_log_le (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    ceilLog 2 (16 / x.beta) ≤ 4 + B1 * p.lambda := by
  have hn : x.n ≤ 2 ^ p.lambda := by
    rw [hs.lambda_eq]
    exact Nat.le_pow_clog (by norm_num) _
  have hp : 16 * x.n ^ B1 ≤ 2 ^ (4 + B1 * p.lambda) := by
    calc
      16 * x.n ^ B1 ≤ 16 * (2 ^ p.lambda) ^ B1 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
      _ = 2 ^ (4 + B1 * p.lambda) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
        congr 1
        ring
  apply (ceilLog_le_iff (by norm_num : 1 < 2) _ _).mpr
  apply (div_le_iff₀ hs.beta_pos).mpr
  calc
    (16 : ℚ) ≤ 16 * (x.beta * (x.n : ℚ) ^ B1) := by nlinarith
    _ = ((16 * x.n ^ B1 : ℕ) : ℚ) * x.beta := by push_cast; ring
    _ ≤ ((2 ^ (4 + B1 * p.lambda) : ℕ) : ℚ) * x.beta := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hs.beta_pos.le

/-- `lem:asymptotics`, paper/paper.tex: the selected
concentration exponent has its literal finite additive upper bound. -/
theorem T_upper_exponent (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.T ≤ p.m * p.k + 2 * p.m + 5 + (B1 + 2) * p.lambda := by
  have hn : x.n ≤ 2 ^ p.lambda := by
    rw [hs.lambda_eq]
    exact Nat.le_pow_clog (by norm_num) _
  have hln : p.lambda ≤ x.n := by
    rw [hs.lambda_eq]
    exact NearCubicGates.Close.Counter.clog_le_self _
  have hJn : p.Jmax ≤ x.n ^ 2 := by
    rw [hs.Jmax_eq]
    have hm := hs.mu_le_lambda
    have hn4 := hs.input_valid.1
    nlinarith
  have hj : p.Jmax * x.n ^ B1 ≤ 2 ^ ((B1 + 2) * p.lambda) := by
    calc
      p.Jmax * x.n ^ B1 ≤ x.n ^ 2 * x.n ^ B1 := Nat.mul_le_mul_right _ hJn
      _ = x.n ^ (B1 + 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ (2 ^ p.lambda) ^ (B1 + 2) := Nat.pow_le_pow_left hn _
      _ = 2 ^ ((B1 + 2) * p.lambda) := by rw [← pow_mul]; congr 1; ring
  let a := p.m * p.k + 2 * p.m + 5
  have hp : (2 ^ a * p.Jmax) * x.n ^ B1 ≤ 2 ^ (a + (B1 + 2) * p.lambda) := by
    calc
      (2 ^ a * p.Jmax) * x.n ^ B1 = 2 ^ a * (p.Jmax * x.n ^ B1) := by ring
      _ ≤ 2 ^ a * 2 ^ ((B1 + 2) * p.lambda) := Nat.mul_le_mul_left _ hj
      _ = 2 ^ (a + (B1 + 2) * p.lambda) := (pow_add _ _ _).symm
  apply (hs.T_le_iff _).mpr
  refine ⟨by omega, ?_⟩
  change ((2 ^ a * p.Jmax : ℕ) : ℚ) ≤ 2 ^ (a + (B1 + 2) * p.lambda) * x.beta
  calc
    ((2 ^ a * p.Jmax : ℕ) : ℚ) ≤
        ((2 ^ a * p.Jmax : ℕ) : ℚ) * (x.beta * (x.n : ℚ) ^ B1) := by
      have hc : 0 ≤ ((2 ^ a * p.Jmax : ℕ) : ℚ) := by positivity
      nlinarith
    _ = (((2 ^ a * p.Jmax) * x.n ^ B1 : ℕ) : ℚ) * x.beta := by push_cast; ring
    _ ≤ 2 ^ (a + (B1 + 2) * p.lambda) * x.beta := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) hs.beta_pos.le

/-- `lem:asymptotics`, paper/paper.tex: the actual
population cutoff has a uniform logarithmic upper bound. -/
theorem tau_upper (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.tau ≤ (B1 + 20) * p.mu * p.lambda := by
  have hp := hs.precision_log_le B1 hb
  have hk := hs.k_le
  have hlogs := hs.logarithms_pos
  have hm := Nat.mul_le_mul_left B1 (Nat.mul_le_mul_right p.lambda hlogs.2)
  rw [hs.tau_eq]
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: the actual
concentration exponent has a uniform logarithmic upper bound. -/
theorem T_upper (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.T ≤ (B1 + 80) * p.mu * p.lambda := by
  have ht := hs.T_upper_exponent B1 hb
  have hk := hs.k_le
  have hlogs := hs.logarithms_pos
  have hm := Nat.mul_le_mul_left (B1 + 2) (Nat.mul_le_mul_right p.lambda hlogs.2)
  rw [hs.m_eq] at ht
  nlinarith

/-- `prop:complete` and `lem:asymptotics`, paper/paper.tex: the first precision side condition holds uniformly
at sufficiently large lengths. -/
theorem eventual_k_precision (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → ceilLog 2 (16 / x.beta) ≤ p.k := by
  obtain ⟨onset, hon, hk⟩ := eventual_k_bounds
  refine ⟨max onset (2 ^ (2 ^ (B1 + 4))), hon.trans (le_max_left _ _), ?_⟩
  intro x p hn hs hb
  have hlow := (hk x p ((le_max_left _ _).trans hn) hs).1
  have hmu : B1 + 4 ≤ p.mu := by
    rw [hs.mu_eq]
    exact mu_large _ _ ((le_max_right _ _).trans hn)
  have hp := hs.precision_log_le B1 hb
  have hmul := Nat.mul_le_mul_right p.lambda hmu
  have hl := hs.logarithms_pos.1
  nlinarith

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: polynomial
precision gives a denominator-independent upper bound for its binary logarithm. -/
theorem precision_log_le (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    ceilLog 2 (16 / x.beta) ≤ 4 + B1 * p.lambda :=
  CoreRules.precision_log_le (hs : CoreRules x p) B1 hb

/-- `lem:asymptotics`, paper/paper.tex: the selected
concentration exponent has its literal finite additive upper bound. -/
theorem T_upper_exponent (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.T ≤ p.m * p.k + 2 * p.m + 5 + (B1 + 2) * p.lambda :=
  CoreRules.T_upper_exponent (hs : CoreRules x p) B1 hb

/-- `lem:asymptotics`, paper/paper.tex: the actual
population cutoff has a uniform logarithmic upper bound. -/
theorem tau_upper (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.tau ≤ (B1 + 20) * p.mu * p.lambda :=
  CoreRules.tau_upper (hs : CoreRules x p) B1 hb

/-- `lem:asymptotics`, paper/paper.tex: the actual
concentration exponent has a uniform logarithmic upper bound. -/
theorem T_upper (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.T ≤ (B1 + 80) * p.mu * p.lambda :=
  CoreRules.T_upper (hs : CoreRules x p) B1 hb

/-- `prop:complete` and `lem:asymptotics`, paper/paper.tex: the first precision side condition holds uniformly
at sufficiently large lengths. -/
theorem eventual_k_precision (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → ParameterRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → ceilLog 2 (16 / x.beta) ≤ p.k := by
  obtain ⟨onset, hon, hbound⟩ := CoreRules.eventual_k_precision B1
  refine ⟨onset, hon, ?_⟩
  intro x p hn hs hb
  exact hbound x p hn (hs : CoreRules x p) hb

end NearQuarticWires.Cells.ParameterRules

