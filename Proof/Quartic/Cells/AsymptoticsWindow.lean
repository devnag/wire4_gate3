import Proof.Quartic.Cells.AsymptoticsCompleteness
import Proof.Gates.Counter.Window
import Proof.Quartic.Cells.ParametersPrimeGrowth

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic
open NearCubicGates

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the literal
integer height has two uniform comparisons with the selected prime scale. -/
theorem height_scale (hs : ParameterRules x p) :
    32 * p.h ≤ p.P ∧ p.P ≤ 64 * p.h := by
  have hP := hs.prime_candidate.1
  rw [hs.h_eq, hs.hE_eq, hs.m_eq]
  omega

/-- `imp:window`, `lem:asymptotics`, and `eq:window`, paper/paper.tex: the actual selected pair window has the quantitative
fourth-power growth bound, dominates the prime scale, and pays the branch
in which the chain's reference length is `h²/(256T)`. -/
theorem eventual_window_geometry
    (B1 : ℕ) :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ (x : ParameterInput) (p : Parameters),
      onset ≤ x.n → ParameterRules x p → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      p.P ≤ 64 * p.h ∧ 2 ≤ p.L2 ∧ p.P ≤ p.L2 - 1 ∧
        p.P ^ 6 ≤ NearCubicGates.Close.Counter.pairGrowthConstant * p.lambda ^ 3 *
          (2 * (p.L2 - 1)) ^ 4 ∧
        487 * p.m * p.h < 256 * (p.Lw - 1) := by
  obtain ⟨op, hop, hp⟩ := eventual_prime_bounds B1
  obtain ⟨og, hog, hg⟩ := PrimeArithmetic.dyadic_pair_growth
  obtain ⟨ol, hol, hl⟩ := NearCubicGates.Close.Counter.polynomial_lambda_binary
    NearCubicGates.Close.Counter.pairGrowthConstant 3
  refine ⟨max op (max ol (2 ^ (4 * og))), by omega, ?_⟩
  intro x p hn hs hb
  have hbinary := (hp x p (by omega) hs hb).1
  have hlog : 4 * og ≤ p.lambda := by
    have h := Nat.clog_mono_right 2 (by omega : 2 ^ (4 * og) ≤ x.n)
    rw [hs.lambda_eq]
    simpa only [NearCubicGates.Target.lambda, Nat.clog_pow 2 _ (by norm_num)] using h
  have hrequired : og ≤ p.P := by
    calc
      og ≤ 2 ^ og := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ (p.lambda / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p.P := hbinary
  have hpaid : NearCubicGates.Close.Counter.pairGrowthConstant * p.lambda ^ 3 ≤ p.P := by
    calc
      _ = NearCubicGates.Close.Counter.pairGrowthConstant *
          (NearCubicGates.Target.lambda x.n) ^ 3 := by rw [hs.lambda_eq]
      _ ≤ 2 ^ (NearCubicGates.Target.lambda x.n / 4) := (hl x.n (by omega)).2
      _ = 2 ^ (p.lambda / 4) := by rw [hs.lambda_eq]
      _ ≤ 2 ^ (p.lambda / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p.P := hbinary
  have hP100 := hs.prime_candidate.1
  have hPn := hs.prime_candidate.2.1
  obtain ⟨hside, hgrowth⟩ := hg p.P x.n hrequired hPn
  have hLeq : p.L2 = NearCubicGates.Close.Counter.pairSide
      (NearCubicGates.ScalarWindow.window (NearCubicGates.Close.Counter.dyadicPrimes p.P)) := by
    rw [hs.L2_eq, hs.Dprime_eq, hs.primes_eq]
  rw [← hLeq] at hside hgrowth
  rw [← hs.lambda_eq] at hgrowth
  have hgap := NearCubicGates.Close.Counter.pair_side_dominates p.P p.lambda p.L2
    (by omega) hpaid hgrowth
  have hLtwo : p.L2 ≤ 2 * (p.L2 - 1) := by omega
  have hheight := hs.height_scale
  have hpos : 0 < p.h := by have := hs.height; have := hs.T_pos; omega
  have hLw := hs.window_bounds.2.2
  refine ⟨hheight.2, hside, by omega, ?_, ?_⟩
  · change p.P ^ 6 ≤ (32 ^ 3 * (16 ^ 3 * 48 ^ 4)) * p.lambda ^ 3 *
      (2 * (p.L2 - 1)) ^ 4
    exact hgrowth.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLtwo 4))
  · rw [hs.m_eq]
    omega

end NearQuarticWires.Cells.ParameterRules
