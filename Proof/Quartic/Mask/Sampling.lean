import Proof.Quartic.Mask.Concrete
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false

namespace NearQuarticWires.Mask

open scoped BigOperators unitInterval
open MeasureTheory ProbabilityTheory Real

/-- Paper `lem:filter`: one common independent Bernoulli choice
for every occurrence of the complete call, not a new draw at each point. -/
noncomputable def selectionLaw (ι : Type*) [Fintype ι] (p : unitInterval) : Measure (ι → Bool) :=
  Measure.pi fun _ : ι => bernoulliMeasure true false p

instance (ι : Type*) [Fintype ι] (p : unitInterval) : IsProbabilityMeasure (selectionLaw ι p) := by
  unfold selectionLaw
  infer_instance

/-- Paper `def:mask`: the actual sampled population at a point
whose nonzero-residual occurrence labels are `active`. -/
def sampledPopulation {ι : Type*} (active : Finset ι) (selection : ι → Bool) : ℕ :=
  (active.filter fun i => selection i = true).card

/-- Paper `lem:filter`: the actual sampled population
is the integer sum of independent selected-occurrence bits. -/
theorem sampledPopulation_cast {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (selection : ι → Bool) :
    (sampledPopulation active selection : ℝ) =
      ∑ i, if i ∈ active then (if selection i then (1 : ℝ) else 0) else 0 := by
  classical
  have hc : sampledPopulation active selection =
      ∑ i ∈ active, (if selection i then (1 : ℕ) else 0) := by
    rw [sampledPopulation, Finset.card_filter]
  rw [hc]
  push_cast
  symm
  rw [← Finset.sum_filter]
  simp

/-- Paper `lem:filter`: the exact MGF on the common whole-call
selection space. This proves the needed binomial behavior directly by Fubini,
retaining the same selection bits at all different cell points. -/
theorem sampledPopulation_mgf {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (p : unitInterval) (t : ℝ) :
    mgf (fun selection => (sampledPopulation active selection : ℝ))
      (selectionLaw ι p) t = ((p : ℝ) * exp t + (1 - (p : ℝ))) ^ active.card := by
  classical
  have hfun : (fun selection : ι → Bool => exp (t * (sampledPopulation active selection : ℝ))) =
      (fun selection => ∏ i, exp (t *
        (if i ∈ active then (if selection i then (1 : ℝ) else 0) else 0))) := by
    funext selection
    rw [sampledPopulation_cast, Finset.mul_sum, Real.exp_sum]
  rw [mgf, hfun, selectionLaw,
    integral_fintype_prod_eq_prod (μ := fun _ : ι => bernoulliMeasure true false p)
      (fun (i : ι) (b : Bool) => exp (t *
        (if i ∈ active then (if b then (1 : ℝ) else 0) else 0)))]
  simp only [integral_bernoulliMeasure, smul_eq_mul]
  calc
    _ = ∏ i : ι, if i ∈ active then ((p : ℝ) * exp t + (1 - (p : ℝ))) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i ∈ active <;> simp [h]
    _ = _ := by simp [Finset.prod_ite_mem]

/-- Paper `lem:filter`: a finite common selection space
makes every exponential tilt integrable; no MGF-integrability premise is left. -/
theorem sampledPopulation_exp_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (p : unitInterval) (t : ℝ) :
    Integrable (fun selection => exp (t * (sampledPopulation active selection : ℝ)))
      (selectionLaw ι p) := by
  classical
  have hfun : (fun selection : ι → Bool => exp (t * (sampledPopulation active selection : ℝ))) =
      (fun selection => ∏ i, exp (t *
        (if i ∈ active then (if selection i then (1 : ℝ) else 0) else 0))) := by
    funext selection
    rw [sampledPopulation_cast, Finset.mul_sum, Real.exp_sum]
  rw [hfun, selectionLaw]
  exact Integrable.fintype_prod (μ := fun _ : ι => bernoulliMeasure true false p)
    (f := fun (i : ι) (b : Bool) => exp (t *
      (if i ∈ active then (if b then (1 : ℝ) else 0) else 0)))
    fun _ => integrable_bernoulliMeasure true false p _

/-- Paper `lem:filter`: the concrete whole-call product
selection has exactly the previously proved binomial MGF bound. -/
theorem sampledPopulation_mgf_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (p : unitInterval) (t : ℝ) :
    mgf (fun selection => (sampledPopulation active selection : ℝ))
      (selectionLaw ι p) t ≤ exp ((active.card : ℝ) * (p : ℝ) * (exp t - 1)) := by
  rw [sampledPopulation_mgf, ← filterLaw_mgf]
  exact filterLaw_mgf_le active.card p t

/-- Paper `lem:filter`: Chernoff upper tilt on the actual
common selection space, with all integrability and MGF bounds discharged. -/
theorem selection_upper_tilt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (p : unitInterval) (t a : ℝ) (ht : 0 ≤ t) :
    (selectionLaw ι p).real {selection | a ≤ (sampledPopulation active selection : ℝ)} ≤
      exp (-t * a + (active.card : ℝ) * (p : ℝ) * (exp t - 1)) := by
  have h := measure_ge_le_exp_mul_mgf (μ := selectionLaw ι p)
    (X := fun selection => (sampledPopulation active selection : ℝ)) a ht
      (sampledPopulation_exp_integrable active p t)
  calc
    _ ≤ exp (-t * a) * mgf (fun selection => (sampledPopulation active selection : ℝ))
        (selectionLaw ι p) t := h
    _ ≤ exp (-t * a) * exp ((active.card : ℝ) * (p : ℝ) * (exp t - 1)) :=
      mul_le_mul_of_nonneg_left (sampledPopulation_mgf_le active p t) (exp_pos _).le
    _ = _ := (exp_add _ _).symm

/-- Paper `lem:filter`: Chernoff lower tilt on the actual
common whole-call selection space. -/
theorem selection_lower_tilt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (p : unitInterval) (t a : ℝ) (ht : t ≤ 0) :
    (selectionLaw ι p).real {selection | (sampledPopulation active selection : ℝ) ≤ a} ≤
      exp (-t * a + (active.card : ℝ) * (p : ℝ) * (exp t - 1)) := by
  have h := measure_le_le_exp_mul_mgf (μ := selectionLaw ι p)
    (X := fun selection => (sampledPopulation active selection : ℝ)) a ht
      (sampledPopulation_exp_integrable active p t)
  calc
    _ ≤ exp (-t * a) * mgf (fun selection => (sampledPopulation active selection : ℝ))
        (selectionLaw ι p) t := h
    _ ≤ exp (-t * a) * exp ((active.card : ℝ) * (p : ℝ) * (exp t - 1)) :=
      mul_le_mul_of_nonneg_left (sampledPopulation_mgf_le active p t) (exp_pos _).le
    _ = _ := (exp_add _ _).symm

/-- Paper `lem:filter` (a): exact printed constant on
the common independent occurrence selection, without a distribution-law premise. -/
theorem selection_small_population {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (τ : ℕ) (p : unitInterval)
    (hmean : (active.card : ℝ) * (p : ℝ) ≤ (τ : ℝ) / 4) :
    (selectionLaw ι p).real {selection | τ < sampledPopulation active selection} ≤
      (exp 1 / 4) ^ (τ + 1) := by
  have hset : {selection : ι → Bool | τ < sampledPopulation active selection} =
      {selection | (τ : ℝ) + 1 ≤ (sampledPopulation active selection : ℝ)} := by
    ext selection
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h
    · exact_mod_cast (show τ + 1 ≤ sampledPopulation active selection by omega)
    · have : τ + 1 ≤ sampledPopulation active selection := by exact_mod_cast h
      omega
  rw [hset]
  have h := selection_upper_tilt active p (log 4) ((τ : ℝ) + 1)
    (log_nonneg (by norm_num))
  rw [exp_log (by norm_num : (0 : ℝ) < 4)] at h
  have he : exp (1 - log (4 : ℝ)) = exp 1 / 4 := by
    rw [exp_sub, exp_log (by norm_num)]
  calc
    _ ≤ exp (-log 4 * ((τ : ℝ) + 1) + (active.card : ℝ) * (p : ℝ) * (4 - 1)) := h
    _ ≤ exp (((τ : ℝ) + 1) * (1 - log 4)) := by
      apply exp_le_exp.mpr
      nlinarith
    _ = (exp 1 / 4) ^ (τ + 1) := by
      rw [← he, ← exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Paper `lem:filter` (b): exact printed lower
tail on the same common selection law. -/
theorem selection_large_population {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (τ : ℕ) (p : unitInterval)
    (hmean : 4 * (τ : ℝ) ≤ (active.card : ℝ) * (p : ℝ)) :
    (selectionLaw ι p).real {selection | sampledPopulation active selection ≤ τ} ≤
      exp (-9 * (τ : ℝ) / 8) := by
  have hset : {selection : ι → Bool | sampledPopulation active selection ≤ τ} =
      {selection | (sampledPopulation active selection : ℝ) ≤ (τ : ℝ)} := by
    ext selection
    simp only [Set.mem_setOf_eq, Nat.cast_le]
  rw [hset]
  have h := selection_lower_tilt active p (-log 2) τ
    (neg_nonpos.mpr (log_nonneg (by norm_num)))
  have he : exp (-log (2 : ℝ)) = 1 / 2 := by
    rw [exp_neg, exp_log (by norm_num)]
    norm_num
  rw [he] at h
  have hlog : log (2 : ℝ) ≤ 7 / 8 := by linarith [log_two_lt_d9]
  have hprod := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg τ : (0 : ℝ) ≤ τ)
  exact h.trans (exp_le_exp.mpr (by nlinarith))

/-- Paper `lem:filter` (c): exact printed
structural tail under the original common occurrence-selection law. -/
theorem selection_structural_population {ι : Type*} [Fintype ι] [DecidableEq ι]
    (active : Finset ι) (Xmax : ℕ) (p : unitInterval)
    (hmean : (active.card : ℝ) * (p : ℝ) ≤ (Xmax : ℝ) / 12) :
    (selectionLaw ι p).real
      {selection | (Xmax : ℝ) / 2 ≤ (sampledPopulation active selection : ℝ)} ≤
      (2 : ℝ) ^ (-(Xmax : ℝ) / 2) := by
  have h := selection_upper_tilt active p (log 4) ((Xmax : ℝ) / 2)
    (log_nonneg (by norm_num))
  rw [exp_log (by norm_num : (0 : ℝ) < 4)] at h
  have hl4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
    norm_num
  have hl2 : (1 : ℝ) / 2 ≤ log 2 := by linarith [log_two_gt_d9]
  have hp := mul_le_mul_of_nonneg_right hl2
    (Nat.cast_nonneg Xmax : (0 : ℝ) ≤ Xmax)
  calc
    _ ≤ exp (-log 4 * ((Xmax : ℝ) / 2) + (active.card : ℝ) * (p : ℝ) * (4 - 1)) := h
    _ ≤ exp (log 2 * (-(Xmax : ℝ) / 2)) := by
      apply exp_le_exp.mpr
      rw [hl4]
      nlinarith
    _ = _ := by rw [Real.rpow_def_of_pos (by norm_num)]

end NearQuarticWires.Mask
