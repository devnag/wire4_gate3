import Statement
import Proof.Gates.FiniteAverages
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The finite Bernstein inequality

Paper: `imp:bernstein` (the bounded-variable Bernstein inequality of Vershynin, Theorem 2.8.4, with `K = 1`), used
in `lem:localize`, paper/paper.tex.

`vershynin18_finiteBernstein` proves the statement input `Vershynin18_Theorem2_8_4_FiniteBernstein`: for independent
variables `Y_i` on a finite uniform sample space with mean zero and `|Y_i| ≤ 1`,
`Pr[|Σ_i Y_i| ≥ s] ≤ 2 exp(-s²/(2(Σ_i E Y_i² + s/3)))`. The proof is the standard one:
* `exp_le_quadratic`: `e^x ≤ 1 + x + x²/(2(1 - |x|/3))` for `|x| < 3` (the exponential series with
  `n! ≥ 2·3^{n-2}`);
* `mean_exp_le`: `E e^{λY} ≤ exp(E Y² · λ²/(2(1 - λ/3)))` for `0 ≤ λ < 3`;
* `mean_prod_indep`: under the independence of the statement, the mean of a product of functions of the
  variables is the product of the means (expansion over the finitely many values);
* `upper_tail`: Markov's inequality for `e^{λ Σ Y}` at `λ = s/(v + s/3)`;
* the two tails.
-/

set_option autoImplicit false

namespace NearQuarticWires.Builder

open Finset
open NearCubicGates.FiniteAverages NearCubicGates.PublishedSources.Witness

/-! ### The exponential bound -/

theorem factorial_lower (n : ℕ) : 2 * 3 ^ n ≤ (n + 2).factorial := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial_succ, pow_succ]
    nlinarith

/-- `e^x ≤ 1 + x + x²/(2(1 - |x|/3))` for `|x| < 3`. -/
theorem exp_le_quadratic (x : ℝ) (hx : |x| < 3) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - |x| / 3)) := by
  have hs := Real.summable_pow_div_factorial x
  have hexp : Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  set r := |x| / 3 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  -- the tail, term by term
  have hterm : ∀ n : ℕ, x ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ x ^ 2 / 2 * r ^ n := by
    intro n
    have hf : (2 : ℝ) * 3 ^ n ≤ ((n + 2).factorial : ℝ) := by exact_mod_cast factorial_lower n
    have hpos : (0 : ℝ) < 2 * 3 ^ n := by positivity
    calc x ^ (n + 2) / ((n + 2).factorial : ℝ) ≤ |x| ^ (n + 2) / ((n + 2).factorial : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          rw [← abs_pow]
          exact le_abs_self _
      _ ≤ |x| ^ (n + 2) / (2 * 3 ^ n) := div_le_div_of_nonneg_left (by positivity) hpos hf
      _ = x ^ 2 / 2 * r ^ n := by
          rw [hr, div_pow, pow_add, sq_abs]
          field_simp
  have htail : Summable fun n : ℕ => x ^ (n + 2) / ((n + 2).factorial : ℝ) :=
    (summable_nat_add_iff 2).mpr hs
  have hgeo : Summable fun n : ℕ => x ^ 2 / 2 * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle := Summable.tsum_le_tsum hterm htail hgeo
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at hle
  rw [hexp, ← hs.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, zero_add, pow_one, Nat.factorial_one]
  have h1r : 0 < 1 - r := by linarith
  have : x ^ 2 / 2 * (1 - r)⁻¹ = x ^ 2 / (2 * (1 - |x| / 3)) := by
    rw [hr]
    field_simp
  linarith

/-! ### Means -/

section Means

variable {Samples : Type*} [Fintype Samples]

theorem mean_nonneg' (f : Samples → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

/-- A product of indicators is the indicator of the conjunction. -/
theorem prod_indicator {ι : Type*} [Fintype ι] (P : ι → Prop) : ∏ i, indicator (P i) = indicator (∀ i, P i) := by
  classical
  by_cases h : ∀ i, P i
  · rw [Finset.prod_eq_one fun i _ => by unfold indicator; rw [if_pos (h i)]]
    unfold indicator
    rw [if_pos h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by unfold indicator; rw [if_neg hi])]
    unfold indicator
    rw [if_neg (fun h => hi (h i))]

/-- **Products of independent variables** (from the event factorization `finiteIndependent`): the mean of a product
of functions of the variables is the product of their means. -/
theorem mean_prod_indep {Terms : Type*} [Fintype Terms] (Y : Terms → Samples → ℝ) (hind : finiteIndependent Y)
    (F : Terms → ℝ → ℝ) : mean (fun x => ∏ i, F i (Y i x)) = ∏ i, mean (fun x => F i (Y i x)) := by
  classical
  unfold finiteIndependent at hind
  let V : Terms → Finset ℝ := fun i => univ.image (Y i)
  have hexp : ∀ i x, F i (Y i x) = ∑ a ∈ V i, F i a * indicator (Y i x = a) := by
    intro i x
    rw [Finset.sum_eq_single (Y i x)]
    · unfold indicator
      rw [if_pos rfl, mul_one]
    · intro a _ ha
      unfold indicator
      rw [if_neg (Ne.symm ha), mul_zero]
    · intro h
      exact absurd (Finset.mem_image_of_mem (Y i) (Finset.mem_univ x)) h
  have hprod : ∀ x, ∏ i, F i (Y i x) = ∑ α ∈ Fintype.piFinset V,
      (∏ i, F i (α i)) * indicator (∀ i ∈ (univ : Finset Terms), Y i x ∈ ({α i} : Set ℝ)) := by
    intro x
    simp_rw [hexp]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.prod_mul_distrib, prod_indicator]
    congr 2
    apply propext
    simp
  have hmean : ∀ i, mean (fun x => F i (Y i x)) = ∑ a ∈ V i, F i a * mean (fun x => indicator (Y i x = a)) := by
    intro i
    simp_rw [hexp i]
    rw [mean_finset_sum]
    exact Finset.sum_congr rfl fun a _ => mean_smul _ _
  simp_rw [hprod]
  rw [mean_finset_sum]
  simp_rw [hmean]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mean_smul, hind univ (fun i => {α i}), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2

variable [Nonempty Samples]

/-- **The Bernstein moment bound**: for `E Y = 0`, `|Y| ≤ 1` and `0 ≤ λ < 3`,
`E e^{λY} ≤ exp(E Y² · λ²/(2(1 - λ/3)))`. -/
theorem mean_exp_le (Y : Samples → ℝ) (hmean : mean Y = 0) (hY : ∀ x, |Y x| ≤ 1) (l : ℝ) (hl0 : 0 ≤ l)
    (hl3 : l < 3) :
    mean (fun x => Real.exp (l * Y x)) ≤ Real.exp (mean (fun x => Y x ^ 2) * (l ^ 2 / (2 * (1 - l / 3)))) := by
  set g := l ^ 2 / (2 * (1 - l / 3)) with hg
  have h13 : 0 < 1 - l / 3 := by linarith
  have hpt : ∀ x, Real.exp (l * Y x) ≤ 1 + l * Y x + Y x ^ 2 * g := by
    intro x
    have hlx : |l * Y x| ≤ l := by
      rw [abs_mul, abs_of_nonneg hl0]
      exact mul_le_of_le_one_right hl0 (hY x)
    have h := exp_le_quadratic (l * Y x) (by linarith)
    refine h.trans ?_
    have hd : 0 < 2 * (1 - |l * Y x| / 3) := by linarith
    have hd' : 2 * (1 - l / 3) ≤ 2 * (1 - |l * Y x| / 3) := by linarith
    have : (l * Y x) ^ 2 / (2 * (1 - |l * Y x| / 3)) ≤ Y x ^ 2 * g := by
      rw [hg, mul_pow, ← mul_div_assoc, mul_comm (Y x ^ 2)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hd'
    linarith
  have hlin : mean (fun x => 1 + l * Y x + Y x ^ 2 * g) = 1 + mean (fun x => Y x ^ 2) * g := by
    rw [mean_add, mean_add, mean_const, mean_smul, hmean]
    unfold mean
    simp only []
    rw [← Finset.sum_mul]
    ring
  calc mean (fun x => Real.exp (l * Y x)) ≤ mean (fun x => 1 + l * Y x + Y x ^ 2 * g) := mean_le_mean _ _ hpt
    _ = 1 + mean (fun x => Y x ^ 2) * g := hlin
    _ ≤ Real.exp (mean (fun x => Y x ^ 2) * g) := by
        have := Real.add_one_le_exp (mean (fun x => Y x ^ 2) * g)
        linarith

/-- **The upper tail**: `Pr[Σ_i Y_i ≥ s] ≤ exp(-s²/(2(v + s/3)))` with `v = Σ_i E Y_i²`. -/
theorem upper_tail {Terms : Type*} [Fintype Terms] (Y : Terms → Samples → ℝ) (hind : finiteIndependent Y)
    (hmean : ∀ i, mean (Y i) = 0) (hY : ∀ i x, |Y i x| ≤ 1) (s : ℝ) (hs : 0 < s) :
    mean (fun x => indicator (s ≤ ∑ i, Y i x)) ≤
      Real.exp (-(s ^ 2) / (2 * ((∑ i, mean (fun x => (Y i x) ^ 2)) + s / 3))) := by
  classical
  set v := ∑ i, mean (fun x => (Y i x) ^ 2) with hv
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun i _ => mean_nonneg' _ fun x => sq_nonneg _
  rcases eq_or_lt_of_le hv0 with hv0' | hvpos
  · -- `v = 0`: every variable vanishes, and the event is empty
    have hzero : ∀ i x, Y i x = 0 := by
      intro i x
      have hi : mean (fun x => (Y i x) ^ 2) = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mean_nonneg' (fun x => (Y i x) ^ 2)
          fun x => sq_nonneg _).mp hv0'.symm i (Finset.mem_univ i)
        exact h
      unfold mean at hi
      have hc : (0 : ℝ) < Fintype.card Samples := by exact_mod_cast Fintype.card_pos
      rw [div_eq_zero_iff, or_iff_left hc.ne'] at hi
      have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => sq_nonneg (Y i x)).mp hi x (Finset.mem_univ x)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    have : mean (fun x => indicator (s ≤ ∑ i, Y i x)) = 0 := by
      unfold mean
      rw [Finset.sum_eq_zero fun x _ => by
        unfold indicator
        rw [if_neg (by simp only [hzero, Finset.sum_const_zero]; linarith)]]
      simp
    rw [this]
    exact (Real.exp_pos _).le
  · -- `v > 0`: Markov's inequality at `λ = s/(v + s/3)`
    set l := s / (v + s / 3) with hl
    have hD : 0 < v + s / 3 := by linarith
    have hl0 : 0 ≤ l := by positivity
    have hl3 : l < 3 := by
      rw [hl, div_lt_iff₀ hD]
      linarith
    have hmarkov : ∀ x, indicator (s ≤ ∑ i, Y i x) ≤ Real.exp (-(l * s)) * ∏ i, Real.exp (l * Y i x) := by
      intro x
      rw [← Real.exp_sum, ← Real.exp_add]
      unfold indicator
      split_ifs with h
      · apply Real.one_le_exp
        rw [← Finset.mul_sum]
        nlinarith
      · exact (Real.exp_pos _).le
    have hprod := mean_prod_indep Y hind (fun _ y => Real.exp (l * y))
    calc mean (fun x => indicator (s ≤ ∑ i, Y i x))
        ≤ mean (fun x => Real.exp (-(l * s)) * ∏ i, Real.exp (l * Y i x)) := mean_le_mean _ _ hmarkov
      _ = Real.exp (-(l * s)) * ∏ i, mean (fun x => Real.exp (l * Y i x)) := by rw [mean_smul, hprod]
      _ ≤ Real.exp (-(l * s)) * ∏ i, Real.exp (mean (fun x => Y i x ^ 2) * (l ^ 2 / (2 * (1 - l / 3)))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact Finset.prod_le_prod (fun i _ => mean_nonneg' _ fun x => (Real.exp_pos _).le)
            fun i _ => mean_exp_le (Y i) (hmean i) (hY i) l hl0 hl3
      _ = Real.exp (-(l * s) + v * (l ^ 2 / (2 * (1 - l / 3)))) := by
          rw [← Real.exp_sum, ← Real.exp_add, hv, Finset.sum_mul]
      _ = Real.exp (-(s ^ 2) / (2 * (v + s / 3))) := by
          congr 1
          have h13 : 1 - l / 3 = v / (v + s / 3) := by
            rw [hl]
            field_simp
            ring
          rw [h13, hl]
          field_simp
          ring

end Means

/-- **The finite Bernstein inequality** (`imp:bernstein`; Vershynin, Theorem 2.8.4 with `K = 1`), proved: for
independent variables on a finite uniform sample space with mean zero and `|Y_i| ≤ 1`,
`Pr[|Σ_i Y_i| ≥ s] ≤ 2 exp(-s²/(2(Σ_i E Y_i² + s/3)))`. -/
theorem vershynin18_finiteBernstein : Vershynin18_Theorem2_8_4_FiniteBernstein := by
  classical
  unfold Vershynin18_Theorem2_8_4_FiniteBernstein
  intro Samples Terms _ _ _ _ Y hind hmean hY s hs
  -- the negated variables
  have hindN : finiteIndependent (fun i x => -Y i x) := by
    unfold finiteIndependent at hind ⊢
    intro S events
    have h := hind S (fun i => {y | -y ∈ events i})
    simpa using h
  have hmeanN : ∀ i, mean (fun x => -Y i x) = 0 := by
    intro i
    have h := mean_smul (-1) (Y i)
    simp only [neg_one_mul] at h
    rw [h, hmean i, neg_zero]
  have hYN : ∀ i x, |-Y i x| ≤ 1 := fun i x => by rw [abs_neg]; exact hY i x
  have hup := upper_tail Y hind hmean hY s hs
  have hdown := upper_tail (fun i x => -Y i x) hindN hmeanN hYN s hs
  simp only [neg_sq] at hdown
  have hsplit : ∀ x, indicator (s ≤ |∑ i, Y i x|) ≤
      indicator (s ≤ ∑ i, Y i x) + indicator (s ≤ ∑ i, -Y i x) := by
    intro x
    rw [Finset.sum_neg_distrib]
    have key : s ≤ |∑ i, Y i x| → s ≤ ∑ i, Y i x ∨ s ≤ -∑ i, Y i x := by
      intro h
      rcases le_abs'.mp h with h1 | h1
      · right
        linarith
      · left
        exact h1
    by_cases h1 : s ≤ |∑ i, Y i x|
    · rcases key h1 with h2 | h2
      · have e1 : indicator (s ≤ |∑ i, Y i x|) = 1 := by unfold indicator; rw [if_pos h1]
        have e2 : indicator (s ≤ ∑ i, Y i x) = 1 := by unfold indicator; rw [if_pos h2]
        rw [e1, e2]
        linarith [indicator_nonneg (s ≤ -∑ i, Y i x)]
      · have e1 : indicator (s ≤ |∑ i, Y i x|) = 1 := by unfold indicator; rw [if_pos h1]
        have e2 : indicator (s ≤ -∑ i, Y i x) = 1 := by unfold indicator; rw [if_pos h2]
        rw [e1, e2]
        linarith [indicator_nonneg (s ≤ ∑ i, Y i x)]
    · have e1 : indicator (s ≤ |∑ i, Y i x|) = 0 := by unfold indicator; rw [if_neg h1]
      rw [e1]
      linarith [indicator_nonneg (s ≤ ∑ i, Y i x), indicator_nonneg (s ≤ -∑ i, Y i x)]
  calc mean (fun x => indicator (s ≤ |∑ i, Y i x|))
      ≤ mean (fun x => indicator (s ≤ ∑ i, Y i x) + indicator (s ≤ ∑ i, -Y i x)) := mean_le_mean _ _ hsplit
    _ = mean (fun x => indicator (s ≤ ∑ i, Y i x)) + mean (fun x => indicator (s ≤ ∑ i, -Y i x)) := mean_add _ _
    _ ≤ _ := by linarith

end NearQuarticWires.Builder
