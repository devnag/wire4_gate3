import Proof.Quartic.Cells.ParametersPrimeDensity
import Proof.Gates.Counter.Eventual

set_option autoImplicit false

namespace NearQuarticWires.Cells.PrimeArithmetic

open Nat Finset
open NearCubicGates

/-- The doubled interval inside the actual dyadic interval,
including odd prime scales, `sec:params`, paper/paper.tex. -/
theorem doubledInterval_subset_dyadic (P : ℕ) :
    doubledIntervalPrimes (P / 2) ⊆ Close.Counter.dyadicPrimes P := by
  intro p hp
  obtain ⟨hinterval, hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hinterval
  apply (Close.Counter.mem_dyadicPrimes P p).mpr
  have hdiv := Nat.div_mul_le_self P 2
  exact ⟨by omega, hprime, by omega⟩

/-- The exact dyadic density needed by the parameter windows,
proved from the elementary binomial bounds without a PNT input,
`lem:asymptotics`, paper/paper.tex. -/
theorem dyadic_density :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      (P : ℝ) / 8 ≤ ((Close.Counter.dyadicPrimes P).card : ℝ) * Real.log (P : ℝ) := by
  refine ⟨2 ^ 19, by norm_num, ?_⟩
  intro P hP
  have hn : (2 : ℕ) ^ 17 ≤ P / 2 := by norm_num at hP ⊢; omega
  have hn0 : (0 : ℝ) < (P / 2 : ℕ) := by exact_mod_cast (by norm_num at hn; omega : 0 < P / 2)
  have hround : (P : ℝ) ≤ ((2 * (P / 2) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : P ≤ 2 * (P / 2) + 1)
  have hsmall := doubledInterval_log_count_lower (P / 2) hn
  have hcard : (doubledIntervalPrimes (P / 2)).card ≤ (Close.Counter.dyadicPrimes P).card :=
    Finset.card_le_card (doubledInterval_subset_dyadic P)
  have hcardR : ((doubledIntervalPrimes (P / 2)).card : ℝ) ≤ (Close.Counter.dyadicPrimes P).card := by
    exact_mod_cast hcard
  have harg : 2 * ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) := by
    exact_mod_cast (by omega : 2 * (P / 2) ≤ P)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 * ((P / 2 : ℕ) : ℝ)) harg
  have hlogP : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (by norm_num at hP; omega : 1 ≤ P))
  calc
    (P : ℝ) / 8 ≤ ((2 * (P / 2) + 1 : ℕ) : ℝ) / 8 := div_le_div_of_nonneg_right hround (by norm_num)
    _ ≤ ((doubledIntervalPrimes (P / 2)).card : ℝ) * Real.log (2 * ((P / 2 : ℕ) : ℝ)) := hsmall
    _ ≤ ((doubledIntervalPrimes (P / 2)).card : ℝ) * Real.log (P : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ ((Close.Counter.dyadicPrimes P).card : ℝ) * Real.log (P : ℝ) :=
      mul_le_mul_of_nonneg_right hcardR hlogP

end NearQuarticWires.Cells.PrimeArithmetic
