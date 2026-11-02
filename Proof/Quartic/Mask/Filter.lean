import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace NearQuarticWires.Mask

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators unitInterval

/-- Paper `lem:filter`: the binomial law of the sampled
population, with its actual finite binomial probabilities. -/
noncomputable def filterLaw (population : ℕ) (p : unitInterval) : Measure ℕ :=
  ProbabilityTheory.binomial population p

instance (N : ℕ) (p : unitInterval) : IsProbabilityMeasure (filterLaw N p) := by
  unfold filterLaw
  infer_instance

/-- Paper `lem:filter`: the exact MGF of the sampled population.
This is proved from Mathlib's finite binomial integral, not assumed as a tail input. -/
theorem filterLaw_mgf (N : ℕ) (p : unitInterval) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (filterLaw N p) t =
      ((p : ℝ) * exp t + (1 - (p : ℝ))) ^ N := by
  rw [mgf, filterLaw, integral_binomial]
  simp only [smul_eq_mul]
  rw [← Nat.range_succ_eq_Iic]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, ← exp_nat_mul]
  ring

/-- Paper `lem:filter`: the elementary exponential MGF bound
for the concrete binomial law, valid for positive and negative tilts. -/
theorem filterLaw_mgf_le (N : ℕ) (p : unitInterval) (t : ℝ) :
    mgf (fun k : ℕ => (k : ℝ)) (filterLaw N p) t ≤
      exp ((N : ℝ) * (p : ℝ) * (exp t - 1)) := by
  rw [filterLaw_mgf]
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hp' : (p : ℝ) ≤ 1 := p.property.2
  have hb : 0 ≤ (p : ℝ) * exp t + (1 - (p : ℝ)) := by positivity
  have hbase : (p : ℝ) * exp t + (1 - (p : ℝ)) ≤
      exp ((p : ℝ) * (exp t - 1)) := by
    have h := Real.add_one_le_exp ((p : ℝ) * (exp t - 1))
    nlinarith
  calc
    _ ≤ exp ((p : ℝ) * (exp t - 1)) ^ N := pow_le_pow_left₀ hb hbase N
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

/-- Paper `lem:filter`: upper-tail Chernoff inequality for
the actual sampled population at any nonnegative tilt. -/
theorem filter_upper_tilt (N : ℕ) (p : unitInterval) (t a : ℝ) (ht : 0 ≤ t) :
    (filterLaw N p).real {k | a ≤ (k : ℝ)} ≤
      exp (-t * a + (N : ℝ) * (p : ℝ) * (exp t - 1)) := by
  have h := measure_ge_le_exp_mul_mgf (μ := filterLaw N p)
    (X := fun k : ℕ => (k : ℝ)) a ht (integrable_binomial _)
  calc
    _ ≤ exp (-t * a) * mgf (fun k : ℕ => (k : ℝ)) (filterLaw N p) t := h
    _ ≤ exp (-t * a) * exp ((N : ℝ) * (p : ℝ) * (exp t - 1)) :=
      mul_le_mul_of_nonneg_left (filterLaw_mgf_le N p t) (exp_pos _).le
    _ = _ := (exp_add _ _).symm

/-- Paper `lem:filter`: lower-tail Chernoff inequality for
the actual sampled population at any nonpositive tilt. -/
theorem filter_lower_tilt (N : ℕ) (p : unitInterval) (t a : ℝ) (ht : t ≤ 0) :
    (filterLaw N p).real {k | (k : ℝ) ≤ a} ≤
      exp (-t * a + (N : ℝ) * (p : ℝ) * (exp t - 1)) := by
  have h := measure_le_le_exp_mul_mgf (μ := filterLaw N p)
    (X := fun k : ℕ => (k : ℝ)) a ht (integrable_binomial _)
  calc
    _ ≤ exp (-t * a) * mgf (fun k : ℕ => (k : ℝ)) (filterLaw N p) t := h
    _ ≤ exp (-t * a) * exp ((N : ℝ) * (p : ℝ) * (exp t - 1)) :=
      mul_le_mul_of_nonneg_left (filterLaw_mgf_le N p t) (exp_pos _).le
    _ = _ := (exp_add _ _).symm

/-- Paper `lem:filter` (a): the printed upper tail,
proved directly at tilt `log 4` for the actual sampled-population law. -/
theorem filter_small_population (N τ : ℕ) (p : unitInterval)
    (hmean : (N : ℝ) * (p : ℝ) ≤ (τ : ℝ) / 4) :
    (filterLaw N p).real {k | τ < k} ≤ (exp 1 / 4) ^ (τ + 1) := by
  have ht : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have hset : {k : ℕ | τ < k} = {k : ℕ | (τ : ℝ) + 1 ≤ (k : ℝ)} := by
    ext k
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h
    · exact_mod_cast (show τ + 1 ≤ k by omega)
    · have : τ + 1 ≤ k := by exact_mod_cast h
      omega
  rw [hset]
  have h := filter_upper_tilt N p (log 4) ((τ : ℝ) + 1) ht
  rw [exp_log (by norm_num : (0 : ℝ) < 4)] at h
  have he : exp (1 - log (4 : ℝ)) = exp 1 / 4 := by
    rw [exp_sub, exp_log (by norm_num)]
  calc
    _ ≤ exp (-log 4 * ((τ : ℝ) + 1) + (N : ℝ) * (p : ℝ) * (4 - 1)) := h
    _ ≤ exp (((τ : ℝ) + 1) * (1 - log 4)) := by
      apply exp_le_exp.mpr
      nlinarith
    _ = (exp 1 / 4) ^ (τ + 1) := by
      rw [← he, ← exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Paper `lem:filter` (b): the printed lower tail,
proved at tilt `-log 2`; no Chernoff premise is imported. -/
theorem filter_large_population (N τ : ℕ) (p : unitInterval)
    (hmean : 4 * (τ : ℝ) ≤ (N : ℝ) * (p : ℝ)) :
    (filterLaw N p).real {k | k ≤ τ} ≤ exp (-9 * (τ : ℝ) / 8) := by
  have ht : -log (2 : ℝ) ≤ 0 := neg_nonpos.mpr (log_nonneg (by norm_num))
  have hset : {k : ℕ | k ≤ τ} = {k : ℕ | (k : ℝ) ≤ (τ : ℝ)} := by
    ext k
    simp only [Set.mem_setOf_eq, Nat.cast_le]
  rw [hset]
  have h := filter_lower_tilt N p (-log 2) τ ht
  have he : exp (-log (2 : ℝ)) = 1 / 2 := by
    rw [exp_neg, exp_log (by norm_num)]
    norm_num
  rw [he] at h
  have hlog : log (2 : ℝ) ≤ 7 / 8 := by linarith [log_two_lt_d9]
  have hprod := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)
  exact h.trans (exp_le_exp.mpr (by nlinarith))

/-- Paper `lem:filter` (c): the printed structural
tail at the real threshold `Xmax/2`, including odd values of `Xmax`. -/
theorem filter_structural_population (N Xmax : ℕ) (p : unitInterval)
    (hmean : (N : ℝ) * (p : ℝ) ≤ (Xmax : ℝ) / 12) :
    (filterLaw N p).real {k | (Xmax : ℝ) / 2 ≤ (k : ℝ)} ≤
      (2 : ℝ) ^ (-(Xmax : ℝ) / 2) := by
  have ht : 0 ≤ log (4 : ℝ) := log_nonneg (by norm_num)
  have h := filter_upper_tilt N p (log 4) ((Xmax : ℝ) / 2) ht
  rw [exp_log (by norm_num : (0 : ℝ) < 4)] at h
  have hl4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
    norm_num
  have hl2 : (1 : ℝ) / 2 ≤ log 2 := by linarith [log_two_gt_d9]
  have hp := mul_le_mul_of_nonneg_right hl2
    (Nat.cast_nonneg Xmax : (0 : ℝ) ≤ Xmax)
  calc
    _ ≤ exp (-log 4 * ((Xmax : ℝ) / 2) + (N : ℝ) * (p : ℝ) * (4 - 1)) := h
    _ ≤ exp (log 2 * (-(Xmax : ℝ) / 2)) := by
      apply exp_le_exp.mpr
      rw [hl4]
      nlinarith
    _ = _ := by rw [Real.rpow_def_of_pos (by norm_num)]

end NearQuarticWires.Mask
