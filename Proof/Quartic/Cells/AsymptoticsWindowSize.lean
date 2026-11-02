import Proof.Quartic.Cells.AsymptoticsSelected
import Proof.Quartic.Cells.ParametersPrimeUpper

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates
open scoped BigOperators

/-- `imp:window` and `lem:asymptotics`, paper/paper.tex: the scalar window has at most twice the maximum prime times
the number of primes, including its constant coefficient. -/
theorem scalarWindow_le_twice_card (primes : Finset ℕ) (P : ℕ)
    (hne : primes.Nonempty) (hP : 0 < P) (hbound : ∀ q ∈ primes, q ≤ P) :
    ScalarWindow.window primes ≤ 2 * P * primes.card := by
  have hsum : ∑ q ∈ primes, (q - 1) ≤ ∑ _q ∈ primes, P := by
    apply Finset.sum_le_sum
    intro q hq
    exact (Nat.sub_le q 1).trans (hbound q hq)
  have hcard : 0 < primes.card := Finset.card_pos.mpr hne
  have hprod : 0 < P * primes.card := Nat.mul_pos hP hcard
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  unfold ScalarWindow.window
  nlinarith only [hsum, hprod]

/-- The upper prime-density consequence used in `lem:asymptotics`,
paper/paper.tex: the actual dyadic prime count times
the natural logarithm is bounded by twice the prime scale. -/
theorem eventual_dyadic_count_upper :
    ∃ onset : ℕ, 2 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      ((NearCubicGates.Close.Counter.dyadicPrimes P).card : ℝ) * Real.log (P : ℝ) ≤ 2 * P := by
  exact PrimeArithmetic.eventual_dyadic_count_upper

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the actual
binary lower bound on the chosen prime scale controls the conversion
between `log P` and the public binary logarithm. -/
theorem lambda_log_two_le (hbinary : 2 ^ (p.lambda / 4 + 1) ≤ p.P) :
    (p.lambda : ℝ) * Real.log 2 ≤ 4 * Real.log (p.P : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpower : (2 : ℝ) ^ (p.lambda / 4 + 1) ≤ p.P := by exact_mod_cast hbinary
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (p.lambda / 4 + 1)) hpower
  rw [Real.log_pow] at hlog
  have hquot : p.lambda ≤ 4 * (p.lambda / 4 + 1) := by omega
  have hquotR : (p.lambda : ℝ) ≤ 4 * ((p.lambda / 4 + 1 : ℕ) : ℝ) := by exact_mod_cast hquot
  nlinarith only [mul_le_mul_of_nonneg_right hquotR hlog2.le, hlog]

/-- `lem:asymptotics`, paper/paper.tex: matching
scalar and pair window scales at the actual selected prime set. The
fourth-power form expresses `L2 = Theta(P^(3/2)/lambda^(3/4))`
without introducing a rounded replacement window. -/
theorem eventual_window_scales
    (B1 : ℕ) :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ (x : ParameterInput) (p : Parameters),
      onset ≤ x.n → ParameterRules x p → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      (p.P ^ 2 ≤ 32 * (p.Dprime - 1) * p.lambda) ∧
      ((p.Dprime : ℝ) * p.lambda * Real.log 2 ≤ 16 * (p.P : ℝ) ^ 2) ∧
      (2 ≤ p.L2 ∧ p.P ^ 6 ≤ (32 ^ 3 * (16 ^ 3 * 48 ^ 4)) * p.lambda ^ 3 * p.L2 ^ 4) ∧
      ((p.L2 : ℝ) ^ 4 * (p.lambda : ℝ) ^ 3 * (Real.log 2) ^ 3 ≤ 32768 * (p.P : ℝ) ^ 6) := by
  obtain ⟨op, hop, hp⟩ := eventual_prime_bounds B1
  obtain ⟨oc, hoc, hc⟩ := eventual_dyadic_count_upper
  obtain ⟨os, hos, hscalar⟩ := PrimeArithmetic.dyadic_window_growth
  obtain ⟨ol, hol, hpair⟩ := PrimeArithmetic.dyadic_pair_growth
  let required := max oc (max os ol)
  refine ⟨max op (2 ^ (4 * required)), by omega, ?_⟩
  intro x p hn hs hb
  have hbinary := (hp x p (by omega) hs hb).1
  have hlog : 4 * required ≤ p.lambda := by
    have h := Nat.clog_mono_right 2 (by omega : 2 ^ (4 * required) ≤ x.n)
    rw [hs.lambda_eq]
    simpa only [NearCubicGates.Target.lambda, Nat.clog_pow 2 _ (by norm_num)] using h
  have hrequired : required ≤ p.P := by
    calc
      required ≤ 2 ^ required := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (p.lambda / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p.P := hbinary
  have hP := hs.prime_maximal
  have hD : p.Dprime = NearCubicGates.ScalarWindow.window
      (NearCubicGates.Close.Counter.dyadicPrimes p.P) := by rw [hs.Dprime_eq, hs.primes_eq]
  have hL : p.L2 = NearCubicGates.Close.Counter.pairSide
      (NearCubicGates.ScalarWindow.window (NearCubicGates.Close.Counter.dyadicPrimes p.P)) := by
    rw [hs.L2_eq, hD]
  have hscalarBound := hscalar p.P x.n (by dsimp [required] at hrequired; omega) hP.2.1
  obtain ⟨hLtwo, hpairBound⟩ := hpair p.P x.n (by dsimp [required] at hrequired; omega) hP.2.1
  rw [← hD, ← hs.lambda_eq] at hscalarBound
  rw [← hL, ← hs.lambda_eq] at hpairBound
  rw [← hL] at hLtwo
  have hcount := hc p.P (by dsimp [required] at hrequired; omega)
  rw [← hs.primes_eq] at hcount
  have hloglower := lambda_log_two_le hbinary
  have hcountL : (p.primes.card : ℝ) * p.lambda * Real.log 2 ≤ 8 * p.P := by
    have h := mul_le_mul_of_nonneg_left hloglower (by positivity : (0 : ℝ) ≤ p.primes.card)
    nlinarith only [h, hcount]
  have hweight : p.Dprime ≤ 2 * p.P * p.primes.card := by
    rw [hs.Dprime_eq]
    apply scalarWindow_le_twice_card p.primes p.P hs.primes_nonempty (by omega)
    intro q hq
    rw [hs.primes_eq] at hq
    exact ((NearCubicGates.Close.Counter.mem_dyadicPrimes p.P q).mp hq).1
  have hweightR : (p.Dprime : ℝ) ≤ 2 * p.P * p.primes.card := by exact_mod_cast hweight
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hDupper : (p.Dprime : ℝ) * p.lambda * Real.log 2 ≤ 16 * (p.P : ℝ) ^ 2 := by
    calc
      _ ≤ (2 * (p.P : ℝ) * p.primes.card) * p.lambda * Real.log 2 := by gcongr
      _ = 2 * (p.P : ℝ) * ((p.primes.card : ℝ) * p.lambda * Real.log 2) := by ring
      _ ≤ 2 * (p.P : ℝ) * (8 * p.P) := mul_le_mul_of_nonneg_left hcountL (by positivity)
      _ = _ := by ring
  have hLupper : p.L2 ^ 4 ≤ 8 * p.Dprime ^ 3 := by
    have hdpos : 1 ≤ p.Dprime := hs.window_bounds.1.trans hs.window_bounds.2.1
    rcases NearCubicGates.Close.Counter.pairSide_spec p.Dprime hdpos with h | h
    · have heq : p.L2 = 1 := hs.L2_eq.trans h.1
      omega
    · have hadm := h.1
      rw [← hs.L2_eq] at hadm
      exact NearCubicGates.QuantitativePairWindow.every_admissible_side_upper _ _ hadm.1 hadm.2
  have hLupperR : (p.L2 : ℝ) ^ 4 ≤ 8 * (p.Dprime : ℝ) ^ 3 := by exact_mod_cast hLupper
  refine ⟨hscalarBound, hDupper, ⟨hLtwo, hpairBound⟩, ?_⟩
  calc
    _ ≤ (8 * (p.Dprime : ℝ) ^ 3) * (p.lambda : ℝ) ^ 3 * (Real.log 2) ^ 3 := by gcongr
    _ = 8 * ((p.Dprime : ℝ) * p.lambda * Real.log 2) ^ 3 := by ring
    _ ≤ 8 * (16 * (p.P : ℝ) ^ 2) ^ 3 := by gcongr
    _ = _ := by ring

end NearQuarticWires.Cells.ParameterRules
