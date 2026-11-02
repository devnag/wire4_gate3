import Proof.Quartic.Cells.ParametersPrimeGrowth
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

namespace NearQuarticWires.Cells.PrimeArithmetic

open Real

/-- The elementary prime-counting upper bound has the constant
used in the window estimates, `lem:asymptotics`, paper/paper.tex. -/
theorem eventual_prime_count_upper :
    ∃ onset : ℕ, 2 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      (Nat.primeCounting P : ℝ) * Real.log (P : ℝ) ≤ 2 * P := by
  have hlog2 := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have heps : (0 : ℝ) < 2 - Real.log 4 := by linarith
  have hbound := Chebyshev.eventually_primeCounting_le (ε := 2 - Real.log 4) heps
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max 2 ⌈R⌉₊, by omega, ?_⟩
  intro P hP
  have hPr : R ≤ (P : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast (by omega : ⌈R⌉₊ ≤ P))
  have hpi := hR (P : ℝ) hPr
  have hpi' : (Nat.primeCounting P : ℝ) ≤ 2 * (P : ℝ) / Real.log (P : ℝ) := by
    simpa only [Nat.floor_natCast, show Real.log 4 + (2 - Real.log 4) = 2 by ring] using hpi
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  exact (le_div_iff₀ hlog).mp hpi'

/-- The actual dyadic prime set satisfies the original upper
window count, with no external density input, `lem:asymptotics`,
paper/paper.tex. -/
theorem eventual_dyadic_count_upper :
    ∃ onset : ℕ, 2 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      ((NearCubicGates.Close.Counter.dyadicPrimes P).card : ℝ) * Real.log (P : ℝ) ≤ 2 * P := by
  obtain ⟨onset, hon, hpi⟩ := eventual_prime_count_upper
  refine ⟨onset, hon, ?_⟩
  intro P hP
  have hlog : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
  have hcard : (NearCubicGates.Close.Counter.dyadicPrimes P).card ≤ Nat.primeCounting P := by
    have h := NearCubicGates.Close.Counter.dyadic_card_add P
    omega
  have hcardR : ((NearCubicGates.Close.Counter.dyadicPrimes P).card : ℝ) ≤ Nat.primeCounting P := by
    exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right hcardR hlog).trans (hpi P hP)

/-- Two-sided Chebyshev bounds on the prime count follow from the
proved dyadic density and elementary upper bound. These are the
only density estimates required by `lem:asymptotics`,
paper/paper.tex. -/
theorem prime_counting_chebyshev_bounds :
    ∃ onset : ℕ, 2 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      (P : ℝ) / (8 * Real.log (P : ℝ)) ≤ Nat.primeCounting P ∧
        (Nat.primeCounting P : ℝ) ≤ 2 * (P : ℝ) / Real.log (P : ℝ) := by
  obtain ⟨a, ha, hlower⟩ := dyadic_density
  obtain ⟨b, hb, hupper⟩ := eventual_prime_count_upper
  refine ⟨max a b, by omega, ?_⟩
  intro P hP
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hcard : (NearCubicGates.Close.Counter.dyadicPrimes P).card ≤ Nat.primeCounting P := by
    have h := NearCubicGates.Close.Counter.dyadic_card_add P
    omega
  have hcardR : ((NearCubicGates.Close.Counter.dyadicPrimes P).card : ℝ) ≤ Nat.primeCounting P := by
    exact_mod_cast hcard
  refine ⟨?_, (le_div_iff₀ hlog).mpr (hupper P (by omega))⟩
  have hcount : (P : ℝ) / 8 ≤ (Nat.primeCounting P : ℝ) * Real.log (P : ℝ) :=
    (hlower P (by omega)).trans (mul_le_mul_of_nonneg_right hcardR hlog.le)
  simpa only [div_div] using (div_le_iff₀ hlog).mpr hcount

end NearQuarticWires.Cells.PrimeArithmetic
