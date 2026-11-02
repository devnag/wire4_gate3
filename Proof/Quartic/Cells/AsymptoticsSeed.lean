import Proof.Quartic.Cells.AsymptoticsSample
import Proof.Quartic.Cells.ParametersDimension

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `prop:complete`, paper/paper.tex:
changing the precision numerator from sixteen to sixty-four adds at most two
to its exact ceiling logarithm. -/
theorem precision_log64_le (beta : ℚ) :
    ceilLog 2 (64 / beta) ≤ ceilLog 2 (16 / beta) + 2 := by
  have hlog := le_pow_ceilLog (by norm_num : 1 < 2) (16 / beta)
  apply (ceilLog_le_iff (by norm_num : 1 < 2) _ _).mpr
  calc
    64 / beta = 4 * (16 / beta) := by ring
    _ ≤ 4 * ((2 ^ ceilLog 2 (16 / beta) : ℕ) : ℚ) := by nlinarith
    _ = ((2 ^ (ceilLog 2 (16 / beta) + 2) : ℕ) : ℚ) := by
      push_cast
      rw [pow_add]
      norm_num
      ring

/-- `prop:complete`, paper/paper.tex:
the second precision side condition follows directly from the selected geometry. -/
theorem Xmax_precision (hs : CoreRules x p) :
    2 * p.k + 2 * ceilLog 2 (64 / x.beta) ≤ p.Xmax := by
  have hs1 : 1 ≤ p.s := by
    rw [← hs.star_s]
    exact hs.starParams.one_le_s
  have hr16 := hs.r_even_large.2
  have hk : 16 ≤ p.k := by rw [hs.k_eq]; nlinarith
  have ht : 16 ≤ p.tau := by rw [hs.tau_eq]; omega
  have hnr : 1 ≤ x.n * p.r := by have := hs.n_pos; nlinarith
  have hbase := Nat.mul_le_mul_left (9 * p.tau ^ 2) hnr
  have hX := (hs.Xmax_le_iff p.Xmax).mp le_rfl
  have hthree : 3 * p.tau ≤ p.Xmax := by nlinarith
  have h64 := precision_log64_le x.beta
  rw [hs.tau_eq] at ht hthree
  omega

/-- `lem:asymptotics`, paper/paper.tex: the exact
extension-field degree is eventually `k`, and the seed length is exactly `8k`. -/
theorem eventual_seed_length (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → p.ellf = p.k ∧ p.S = 8 * p.k := by
  obtain ⟨onset, hon, hk⟩ := eventual_k_bounds
  let cQ := 2 * B1 + 100
  refine ⟨max onset (2 ^ (2 ^ (cQ + 1))), hon.trans (le_max_left _ _), ?_⟩
  intro x p hn hs hb
  have hlow := (hk x p ((le_max_left _ _).trans hn) hs).1
  have hmu : cQ + 1 ≤ p.mu := by
    rw [hs.mu_eq]
    exact mu_large _ _ ((le_max_right _ _).trans hn)
  have hq := hs.Qexp_four_upper B1 hb
  change 4 * p.Qexp ≤ 3 * p.k + 4 * cQ * p.lambda at hq
  have hl := hs.logarithms_pos.1
  have hmul := Nat.mul_le_mul_right p.lambda hmu
  have hqk : p.Qexp + 1 ≤ p.k := by nlinarith
  have he : p.ellf = p.k := by rw [hs.ellf_eq, max_eq_left hqk]
  refine ⟨he, ?_⟩
  rw [hs.S_eq, hs.m_eq, he]

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `prop:complete`, paper/paper.tex:
changing the precision numerator from sixteen to sixty-four adds at most two
to its exact ceiling logarithm. -/
theorem precision_log64_le (beta : ℚ) :
    ceilLog 2 (64 / beta) ≤ ceilLog 2 (16 / beta) + 2 :=
  CoreRules.precision_log64_le beta

/-- `prop:complete`, paper/paper.tex:
the second precision side condition follows directly from the selected geometry. -/
theorem Xmax_precision (hs : ParameterRules x p) :
    2 * p.k + 2 * ceilLog 2 (64 / x.beta) ≤ p.Xmax :=
  CoreRules.Xmax_precision (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the exact
extension-field degree is eventually `k`, and the seed length is exactly `8k`. -/
theorem eventual_seed_length (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → ParameterRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → p.ellf = p.k ∧ p.S = 8 * p.k := by
  obtain ⟨onset, hon, hbound⟩ := CoreRules.eventual_seed_length B1
  refine ⟨onset, hon, ?_⟩
  intro x p hn hs hb
  exact hbound x p hn (hs : CoreRules x p) hb

end NearQuarticWires.Cells.ParameterRules

