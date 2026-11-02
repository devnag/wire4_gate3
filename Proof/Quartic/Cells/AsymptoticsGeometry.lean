import Proof.Quartic.Cells.ParametersStars

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates

/-- `lem:asymptotics`, paper/paper.tex: a finite binary
comparison gives the required lower bound for the actual inner dimension. -/
theorem inner_lower_of_binary (n : ℕ) (hn : 4 ≤ n) (hL : 16 ≤ Target.lambda n)
    (hb : 16 * Target.lambda n ≤ 2 ^ (Target.lambda n / 4)) :
    8 * Target.mu n * Target.lambda n ≤
      16 * Target.mu n * Nat.log 2 (n / (16 * Target.mu n) + 1) := by
  let L := Target.lambda n
  let M := Target.mu n
  have hM : 1 ≤ M := NearCubicGates.Close.Transfer.mu_ge_one hn
  have hML : M ≤ L := NearCubicGates.Close.Counter.clog_le_self _
  have hr : 0 < 16 * M := by omega
  have hrb : 16 * M ≤ 2 ^ (L / 4) := (Nat.mul_le_mul_left 16 hML).trans hb
  have hlexp : L / 4 + (L + 1) / 2 ≤ L - 1 := by change 16 ≤ L at hL; omega
  have hnp : 2 ^ (L - 1) < n := by
    simpa only [L, Target.lambda, Nat.pred_eq_sub_one] using
      (Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < n))
  have hprod : 16 * M * 2 ^ ((L + 1) / 2) ≤ n := by
    calc
      16 * M * 2 ^ ((L + 1) / 2) ≤ 2 ^ (L / 4) * 2 ^ ((L + 1) / 2) :=
        Nat.mul_le_mul_right _ hrb
      _ = 2 ^ (L / 4 + (L + 1) / 2) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hlexp
      _ ≤ n := hnp.le
  have hd : 2 ^ ((L + 1) / 2) ≤ n / (16 * M) := by
    apply (Nat.le_div_iff_mul_le hr).mpr
    simpa only [Nat.mul_comm] using hprod
  have hs : (L + 1) / 2 ≤ Nat.log 2 (n / (16 * M) + 1) :=
    Nat.le_log_of_pow_le (by norm_num) (hd.trans (Nat.le_succ _))
  have hhalf : L ≤ 2 * ((L + 1) / 2) := by omega
  change 8 * M * L ≤ 16 * M * Nat.log 2 (n / (16 * M) + 1)
  calc
    8 * M * L ≤ 8 * M * (2 * ((L + 1) / 2)) := Nat.mul_le_mul_left _ hhalf
    _ = 16 * M * ((L + 1) / 2) := by ring
    _ ≤ 16 * M * Nat.log 2 (n / (16 * M) + 1) := Nat.mul_le_mul_left _ hs

/-- `lem:asymptotics`, paper/paper.tex: the inner
dimension's lower estimate holds uniformly at all sufficiently large lengths. -/
theorem eventual_inner_lower :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ n : ℕ, onset ≤ n →
      8 * Target.mu n * Target.lambda n ≤
        16 * Target.mu n * Nat.log 2 (n / (16 * Target.mu n) + 1) := by
  obtain ⟨onset, hon, hbound⟩ := NearCubicGates.Close.Counter.polynomial_lambda_binary 16 1
  refine ⟨onset, by omega, fun n hn => ?_⟩
  obtain ⟨hL, hb⟩ := hbound n hn
  simp only [pow_one] at hb
  exact inner_lower_of_binary n (by omega) hL hb

/-- `lem:asymptotics`, paper/paper.tex: the second
logarithm eventually exceeds any prescribed fixed integer. -/
theorem mu_large (B n : ℕ) (hn : 2 ^ (2 ^ B) ≤ n) : B ≤ Target.mu n := by
  have hL : 2 ^ B ≤ Target.lambda n := by
    have h := Nat.clog_mono_right 2 hn
    simpa only [Nat.clog_pow 2 _ (by norm_num), Target.lambda] using h
  have h := Nat.clog_mono_right 2 hL
  simpa only [Nat.clog_pow 2 _ (by norm_num), Target.mu] using h

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

/-- `lem:asymptotics`, paper/paper.tex: uniform matching
bounds for the selected inner dimension, with explicit constants. -/
theorem eventual_k_bounds : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      8 * p.mu * p.lambda ≤ p.k ∧ p.k ≤ 16 * p.mu * p.lambda := by
  obtain ⟨onset, hon, hb⟩ := eventual_inner_lower
  refine ⟨onset, hon, fun x p hn hs => ⟨?_, hs.k_le⟩⟩
  rw [hs.k_eq, hs.s_eq, hs.r_eq, hs.mu_eq, hs.lambda_eq]
  exact hb x.n hn

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

/-- `lem:asymptotics`, paper/paper.tex: uniform matching
bounds for the selected inner dimension, with explicit constants. -/
theorem eventual_k_bounds : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → ParameterRules x p →
      8 * p.mu * p.lambda ≤ p.k ∧ p.k ≤ 16 * p.mu * p.lambda := by
  obtain ⟨onset, hon, hbound⟩ := CoreRules.eventual_k_bounds
  refine ⟨onset, hon, ?_⟩
  intro x p hn hs
  exact hbound x p hn (hs : CoreRules x p)

end NearQuarticWires.Cells.ParameterRules

