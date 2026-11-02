import Proof.Quartic.Cells.ParametersEventual
import Proof.Quartic.Machine.BudgetArithmetic

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

/-- `prop:time`, paper/paper.tex: the actual inner
dimension and sample exponent eventually pay all three exact exponent
comparisons in the displayed running-time sum, for every fixed polynomial
overhead and every normalized public input. -/
theorem eventual_time_headroom (B1 overhead : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      ((2 * p.Jmax + overhead + p.mu) * p.lambda + 2 ≤ p.k) ∧
      (p.Qexp + (overhead + p.mu) * p.lambda + 2 ≤ p.k) ∧
      (10 * p.k + (overhead + p.mu) * p.lambda + 2 ≤ x.n) := by
  obtain ⟨ok, hok, hk⟩ := eventual_k_bounds
  obtain ⟨onum, hon, hnum⟩ := NearCubicGates.Close.Closure.lambda_poly_lt (overhead + 200) 2
  let B := 2 * B1 + 100 + overhead + 10
  refine ⟨max ok (max onum (2 ^ (2 ^ B))), by omega, ?_⟩
  intro x p hn hs hb
  obtain ⟨hklow, hkup⟩ := hk x p (by omega) hs
  have hq := hs.Qexp_four_upper B1 hb
  have hlogs := hs.logarithms_pos
  have hmu : B ≤ p.mu := by
    rw [hs.mu_eq]
    exact mu_large B x.n (by omega)
  have hpoly : (overhead + 200) * p.lambda ^ 2 ≤ x.n := by
    rw [hs.lambda_eq]
    exact (hnum x.n (by omega)).le
  have hsmall : 2 * B1 + 100 + overhead + p.mu + 2 ≤ 2 * p.mu := by dsimp [B] at hmu; omega
  have hsmallL := Nat.mul_le_mul_right p.lambda hsmall
  have hfirst : (2 * p.Jmax + overhead + p.mu) * p.lambda + 2 ≤ p.k := by
    rw [hs.Jmax_eq]
    dsimp [B] at hmu
    nlinarith only [hklow, hsmallL, hlogs.1, hmu]
  have hsecond : p.Qexp + (overhead + p.mu) * p.lambda + 2 ≤ p.k := by
    nlinarith only [hq, hklow, hsmallL, hlogs.1]
  have hmul := Nat.mul_le_mul_right p.lambda hs.mu_le_lambda
  have hLsquare : p.lambda ≤ p.lambda ^ 2 := by nlinarith only [hlogs.1]
  have hover := Nat.mul_le_mul_left overhead hLsquare
  have hthird : 10 * p.k + (overhead + p.mu) * p.lambda + 2 ≤ x.n := by
    nlinarith only [hkup, hmul, hover, hpoly, hlogs.1]
  exact ⟨hfirst, hsecond, hthird⟩

/-- `prop:time`, paper/paper.tex: the exact stated
three-term running-time envelope is eventually at most `2^n/n^mu` for
the actual computed public scales. The program-to-envelope bound is a
separate implementation obligation. -/
theorem eventual_time_envelope (B1 overhead : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda overhead * x.n ^ p.mu ≤ 2 ^ x.n := by
  obtain ⟨onset, hon, h⟩ := eventual_time_headroom B1 overhead
  refine ⟨onset, hon, ?_⟩
  intro x p hn hs hb
  obtain ⟨hfirst, hsecond, hthird⟩ := h x p hn hs hb
  apply Machine.propTimeEnvelope_fast_of_headroom x.n p.k p.Q p.Jmax p.lambda overhead p.mu p.Qexp
    (by omega) ?_ ?_ hfirst hsecond hthird
  · rw [hs.lambda_eq]
    exact Nat.le_pow_clog (by norm_num) _
  · rw [hs.Q_eq]

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: every sufficiently large normalized public input has actual
canonically selected parameters whose three-term envelope satisfies the
counter's fast bound, independently of the completeness wire cap. -/
theorem eventual_prepared_time (B1 overhead : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      ∃ p, prepare x = some p ∧ ParameterRules x p ∧
        Machine.propTimeEnvelope x.n p.k p.Q p.Jmax p.lambda overhead *
          x.n ^ NearCubicGates.Target.mu x.n ≤ 2 ^ x.n := by
  obtain ⟨os, hos, hs⟩ := eventual_prepare B1
  obtain ⟨ot, hot, ht⟩ := CoreRules.eventual_time_envelope B1 overhead
  refine ⟨max os ot, by omega, ?_⟩
  intro x hn hv hb
  obtain ⟨p, hp, hr⟩ := hs x (by omega) hv hb
  have hbound := ht x p (by omega) (hr : CoreRules x p) hb
  rw [hr.mu_eq] at hbound
  exact ⟨p, hp, hr, hbound⟩

end NearQuarticWires.Cells
