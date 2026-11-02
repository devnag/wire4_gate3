import Proof.Quartic.Cells.ParametersPrimeDyadic

set_option autoImplicit false

namespace NearQuarticWires.Cells.PrimeArithmetic

open Real

/-- The elementary logarithmic error bound behind Bertrand's
binomial argument, used for `lem:asymptotics`, paper/paper.tex. -/
theorem bertrand_log_error_bound (x : ℝ) (hx : 512 ≤ x) :
    log x + sqrt (2 * x) * log (2 * x) ≤ (x / 3) * log 4 := by
  have hx0 : 0 < x := by linarith
  have h := Bertrand.real_main_inequality hx
  have hlog := Real.log_le_log (by positivity : 0 < x * (2 * x) ^ sqrt (2 * x) * (4 : ℝ) ^ (2 * x / 3)) h
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity), Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at hlog
  nlinarith only [hlog]

/-- A convenient elementary lower bound for the fixed logarithm
in the dyadic density proof, `lem:asymptotics`, paper/paper.tex. -/
theorem log_four_ge_one : 1 ≤ log (4 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith

/-- Applying the proved Bertrand inequality at one sixty-fourth
of the input leaves a fixed density margin. This finite bound
replaces a prime-number asymptotic input in `lem:asymptotics`,
paper/paper.tex. -/
theorem scaled_log_error_bound (n : ℝ) (hn : (2 : ℝ) ^ (17 : ℕ) ≤ n) :
    log n + sqrt (2 * n) * log (2 * n) ≤ n * log 4 / 16 := by
  have hn0 : 0 < n := by norm_num at hn; linarith
  have hx : (512 : ℝ) ≤ n / 64 := by norm_num at hn; linarith
  have hlog2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : 17 * log (2 : ℝ) ≤ log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (17 : ℕ)) hn
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hlogx : log (n / 64) = log n - 6 * log (2 : ℝ) := by
    rw [Real.log_div hn0.ne' (by norm_num), show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog2x : log (2 * (n / 64)) = log n - 5 * log (2 : ℝ) := by
    rw [show 2 * (n / 64) = n / 32 by ring, Real.log_div hn0.ne' (by norm_num),
      show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog2n : log (2 * n) = log n + log (2 : ℝ) := by
    rw [Real.log_mul (by norm_num) hn0.ne']
    ring
  have hsqrt : sqrt (2 * n) = 8 * sqrt (2 * (n / 64)) := by
    have h64 : sqrt (64 : ℝ) = 8 := by
      calc
        sqrt (64 : ℝ) = sqrt ((8 : ℝ) ^ 2) := congrArg sqrt (by norm_num)
        _ = 8 := Real.sqrt_sq (by norm_num)
    rw [show 2 * n = 64 * (2 * (n / 64)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64), h64]
  have hsmall : log n ≤ 12 * log (n / 64) := by
    rw [hlogx]
    nlinarith only [hlogn, hlog2.le]
  have hlogs : 8 * log (2 * n) ≤ 12 * log (2 * (n / 64)) := by
    rw [hlog2n, hlog2x]
    nlinarith only [hlogn]
  have hproduct : sqrt (2 * n) * log (2 * n) ≤
      12 * sqrt (2 * (n / 64)) * log (2 * (n / 64)) := by
    rw [hsqrt]
    have h := mul_le_mul_of_nonneg_left hlogs (Real.sqrt_nonneg (2 * (n / 64)))
    nlinarith only [h]
  have hbase := bertrand_log_error_bound (n / 64) hx
  calc
    log n + sqrt (2 * n) * log (2 * n) ≤
        12 * (log (n / 64) + sqrt (2 * (n / 64)) * log (2 * (n / 64))) := by
      nlinarith only [hsmall, hproduct]
    _ ≤ 12 * ((n / 64) / 3 * log 4) := mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = n * log 4 / 16 := by ring

end NearQuarticWires.Cells.PrimeArithmetic
