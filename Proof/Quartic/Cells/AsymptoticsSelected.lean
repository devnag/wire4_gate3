import Proof.Quartic.Cells.AsymptoticsCap

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the actual
greatest printing degree satisfies the exact scaled upper bound. -/
theorem degree_upper_scaled (hs : ParameterRules x p) :
    100 * p.lambda * p.Dmax ≤ x.n := by
  have hpass := hs.degree_maximal.1
  have hlog := hs.clog_Uocc_bounds.1
  change 100 * (p.m * p.k + 2 + p.Dmax * Nat.clog 2 p.Uocc) ≤ x.n - p.k at hpass
  have hm := Nat.mul_le_mul_left p.Dmax hlog
  nlinarith [Nat.sub_le x.n p.k]

/-- `lem:asymptotics`, paper/paper.tex: the numerator
forces a lift exponent of order `mu` whenever the inner dimension has its
proved lower bound. -/
theorem lift_lower_scaled (hs : ParameterRules x p) (hk : 8 * p.mu * p.lambda ≤ p.k) :
    160 * p.mu ≤ p.e := by
  have hlow := CoreRules.lift_lower (hs : CoreRules x p) p.P p.e hs.prime_candidate.2.1 hs.lift_spec.1
  have hl : 0 < p.lambda := by have := hs.logarithms_pos.1; omega
  apply Nat.le_of_mul_le_mul_right (c := p.lambda) (hc := hl)
  nlinarith only [hk, hlow]

/-- `lem:asymptotics`, paper/paper.tex: the actual
prime-budget comparison gives the matching upper scale
`P = O(n/(lambda mu²))` without replacing the greatest chosen candidate. -/
theorem prime_upper_scaled (hs : ParameterRules x p) (he : 160 * p.mu ≤ p.e) :
    16000 * p.lambda * p.mu ^ 2 * p.P ≤ x.n := by
  have hbudget := hs.prime_budget
  have hlogs := hs.logarithms_pos
  have hep : 1 ≤ p.e := hs.e_pos
  have hefactor : 160 * p.mu ≤ 2 * p.e - 1 := by omega
  have hJ : 2 * p.mu ≤ 2 * p.Jmax + 2 := by rw [hs.Jmax_eq]; omega
  have hP := hs.prime_candidate.1
  have hcost : 160 * p.mu ^ 2 * p.P ≤ p.Dmax := by
    calc
      _ ≤ (160 * p.mu) * (2 * p.mu) * (p.P - 1) := by
        have hPP : p.P ≤ 2 * (p.P - 1) := by omega
        have hmul := Nat.mul_le_mul_left (160 * p.mu ^ 2) hPP
        nlinarith only [hmul]
      _ ≤ (2 * p.e - 1) * (2 * p.Jmax + 2) * (p.P - 1) := by gcongr
      _ ≤ p.Dmax := by omega
  calc
    _ = 100 * p.lambda * (160 * p.mu ^ 2 * p.P) := by ring
    _ ≤ 100 * p.lambda * p.Dmax := Nat.mul_le_mul_left _ hcost
    _ ≤ x.n := hs.degree_upper_scaled

/-- `lem:asymptotics`, paper/paper.tex: both actual
selected quantities have uniform matching scales, `e = Theta(mu)` and
`P = Theta(n/(lambda mu²))`, with explicit inequalities. -/
theorem eventual_lift_prime_scales (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → ParameterRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      (160 * p.mu ≤ p.e ∧ p.e ≤ 8 * (32 * B1 + 2200) * p.mu) ∧
      (16000 * p.lambda * p.mu ^ 2 * p.P ≤ x.n ∧
        x.n ≤ primeScaleCoefficient B1 * p.lambda * p.mu ^ 2 * p.P) := by
  obtain ⟨ok, hok, hk⟩ := eventual_k_bounds
  obtain ⟨op, hop, hp⟩ := eventual_prime_bounds B1
  refine ⟨max ok (max op (2 ^ 16)), by omega, ?_⟩
  intro x p hn hs hb
  have helow := hs.lift_lower_scaled (hk x p (by omega) hs).1
  obtain ⟨hbinary, hprice⟩ := hp x p (by omega) hs hb
  have hL : 16 ≤ p.lambda := by
    have h := Nat.clog_mono_right 2 (by omega : 2 ^ (16 : ℕ) ≤ x.n)
    rw [hs.lambda_eq]
    simpa only [NearCubicGates.Target.lambda, Nat.clog_pow 2 16 (by norm_num)] using h
  obtain ⟨e, he, _, hebound⟩ := CoreRules.liftExponent_le_trial (hs : CoreRules x p) B1 hb p.P hbinary hL
  have heq : e = p.e := Option.some.inj (he.symm.trans hs.e_eq)
  subst e
  exact ⟨⟨helow, hebound⟩, hs.prime_upper_scaled helow, hprice⟩

end NearQuarticWires.Cells.ParameterRules
