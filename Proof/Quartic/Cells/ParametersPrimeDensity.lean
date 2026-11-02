import Proof.Quartic.Cells.ParametersPrimeLogBound

set_option autoImplicit false

namespace NearQuarticWires.Cells.PrimeArithmetic

open Nat Real

/-- The exact binomial-factor bound gives a lower bound on the
number of primes in a doubled interval, `lem:asymptotics`,
paper/paper.tex, without a prime-number theorem
assumption. -/
theorem doubledInterval_log_count_lower (n : ℕ) (hn : (2 : ℕ) ^ 17 ≤ n) :
    ((2 * n + 1 : ℕ) : ℝ) / 8 ≤
      ((doubledIntervalPrimes n).card : ℝ) * Real.log (2 * (n : ℝ)) := by
  have hn4 : 4 ≤ n := by norm_num at hn; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htwo : (0 : ℝ) < 2 * (n : ℝ) := by positivity
  have hbin := centralBinom_interval_count_bound n (by omega)
  have hnat : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
      (2 * n) ^ (doubledIntervalPrimes n).card) :=
    (Nat.four_pow_lt_mul_centralBinom n hn4).trans_le (Nat.mul_le_mul_left n hbin)
  have hreal : (4 : ℝ) ^ n < (n : ℝ) *
      ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3) *
        (2 * (n : ℝ)) ^ (doubledIntervalPrimes n).card) := by exact_mod_cast hnat
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (4 : ℝ) ^ n) hreal
  rw [Real.log_pow, Real.log_mul hn0.ne' (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow] at hlog
  have hnreal : (2 : ℝ) ^ (17 : ℕ) ≤ n := by exact_mod_cast hn
  have herr := scaled_log_error_bound (n : ℝ) hnreal
  have hlogtwo : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * n))
  have hroot : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Real.nat_sqrt_le_real_sqrt (a := 2 * n))
  have hsmall : Real.log (n : ℝ) + (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ)) ≤
      (n : ℝ) * Real.log 4 / 16 := by
    have hm := mul_le_mul_of_nonneg_right hroot hlogtwo
    nlinarith only [hm, herr]
  have hfloor : ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / 3 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    exact_mod_cast Nat.div_mul_le_self (2 * n) 3
  have hfloorLog := mul_le_mul_of_nonneg_right hfloor
    (log_four_ge_one.trans' (by norm_num : (0 : ℝ) ≤ 1))
  have hcount : 13 / 48 * (n : ℝ) * Real.log 4 <
      ((doubledIntervalPrimes n).card : ℝ) * Real.log (2 * (n : ℝ)) := by
    nlinarith only [hlog, hsmall, hfloorLog]
  have hmargin : ((2 * n + 1 : ℕ) : ℝ) / 8 ≤ 13 / 48 * (n : ℝ) * Real.log 4 := by
    have h := mul_le_mul_of_nonneg_left log_four_ge_one
      (by positivity : (0 : ℝ) ≤ 13 / 48 * (n : ℝ))
    have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast (by omega : 6 ≤ n)
    push_cast
    nlinarith only [h, hn6]
  exact hmargin.trans hcount.le

end NearQuarticWires.Cells.PrimeArithmetic
