import Proof.Quartic.Cells.ParametersPrimeWindow

set_option autoImplicit false

namespace NearQuarticWires.Cells.PrimeArithmetic

open NearCubicGates
open NearCubicGates.Close.Counter (dyadicPrimes dyadic_weight_lower log_le_lambda pairSide pairSide_growth)

/-- The scalar window has the original quantitative growth bound
with no prime-density input, `lem:asymptotics`, paper/paper.tex. -/
theorem dyadic_window_density :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      (P : ℝ) ^ 2 / 32 ≤ ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) * Real.log (P : ℝ) := by
  obtain ⟨onset, bound, density⟩ := dyadic_density
  refine ⟨onset, bound, ?_⟩
  intro P large
  have PBound : 256 ≤ P := bound.trans large
  have logPositive : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have weight : (P : ℝ) * ((dyadicPrimes P).card : ℝ) ≤
      4 * ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) := by
    exact_mod_cast dyadic_weight_lower P (by omega)
  have multiply := mul_le_mul_of_nonneg_right weight logPositive.le
  have lower := mul_le_mul_of_nonneg_left (density P large) (by positivity : (0 : ℝ) ≤ P)
  nlinarith

/-- The actual dyadic prime set is nonempty at all sufficiently
large scales, without an external density premise, `sec:params`,
paper/paper.tex. -/
theorem dyadic_nonempty :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P → (dyadicPrimes P).Nonempty := by
  obtain ⟨onset, bound, density⟩ := dyadic_density
  refine ⟨onset, bound, ?_⟩
  intro P large
  apply Finset.card_pos.mp
  by_contra empty
  have hz : (dyadicPrimes P).card = 0 := by omega
  have hP : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have lower := density P large
  rw [hz] at lower
  norm_num at lower
  linarith

/-- The scalar window pays the binary logarithm with the original
constant, `imp:window` and `lem:asymptotics`, paper/paper.tex. -/
theorem dyadic_window_growth :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P n : ℕ, onset ≤ P → P ≤ n →
      P ^ 2 ≤ 32 * (ScalarWindow.window (dyadicPrimes P) - 1) * Target.lambda n := by
  obtain ⟨onset, positive, density⟩ := dyadic_window_density
  refine ⟨onset, positive, ?_⟩
  intro P n large small
  have logarithm := log_le_lambda P n (by omega) small
  have lower := density P large
  have scale := mul_le_mul_of_nonneg_left logarithm
    (by positivity : (0 : ℝ) ≤ (ScalarWindow.window (dyadicPrimes P) - 1 : ℕ))
  have realBound : (P : ℝ) ^ 2 ≤
      32 * ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) * (Target.lambda n : ℝ) := by linarith
  exact_mod_cast realBound

/-- The same scalar window dominates its scale linearly,
`imp:window`, paper/paper.tex. -/
theorem dyadic_window_linear :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P : ℕ, onset ≤ P →
      P ≤ 32 * (ScalarWindow.window (dyadicPrimes P) - 1) := by
  obtain ⟨onset, positive, density⟩ := dyadic_window_density
  refine ⟨onset, positive, ?_⟩
  intro P large
  have positiveP : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have logarithm : Real.log (P : ℝ) ≤ P := by
    have h := Real.log_le_sub_one_of_pos positiveP
    linarith
  have scale := mul_le_mul_of_nonneg_left logarithm
    (by positivity : (0 : ℝ) ≤ (ScalarWindow.window (dyadicPrimes P) - 1 : ℕ))
  have lower := density P large
  have realBound : (P : ℝ) ≤ 32 * ((ScalarWindow.window (dyadicPrimes P) - 1 : ℕ) : ℝ) := by nlinarith
  exact_mod_cast realBound

/-- The pair window retains its original fourth-power growth
constant with no prime-number theorem input, `imp:window` and
`lem:asymptotics`, paper/paper.tex. -/
theorem dyadic_pair_growth :
    ∃ onset : ℕ, 256 ≤ onset ∧ ∀ P n : ℕ, onset ≤ P → P ≤ n →
      2 ≤ pairSide (ScalarWindow.window (dyadicPrimes P)) ∧
      P ^ 6 ≤ (32 ^ 3 * (16 ^ 3 * 48 ^ 4)) * (Target.lambda n) ^ 3 *
        (pairSide (ScalarWindow.window (dyadicPrimes P))) ^ 4 := by
  obtain ⟨a, aBound, scalar⟩ := dyadic_window_growth
  obtain ⟨b, bBound, linear⟩ := dyadic_window_linear
  obtain ⟨c, cBound, pair⟩ := pairSide_growth
  refine ⟨max (max a b) (32 * c ^ 4 + 256), ?_, ?_⟩
  · exact (by omega : 256 ≤ 32 * c ^ 4 + 256).trans (le_max_right _ _)
  intro P n large small
  have scalarBound := scalar P n ((le_max_left _ _).trans ((le_max_left _ _).trans large)) small
  have linearBound := linear P ((le_max_right _ _).trans ((le_max_left _ _).trans large))
  have PBound := (le_max_right _ _).trans large
  have windowLarge : c ^ 4 ≤ ScalarWindow.window (dyadicPrimes P) := by omega
  obtain ⟨side, growth⟩ := pair _ windowLarge
  refine ⟨side, ?_⟩
  calc
    P ^ 6 = (P ^ 2) ^ 3 := by ring
    _ ≤ (32 * (ScalarWindow.window (dyadicPrimes P) - 1) * Target.lambda n) ^ 3 :=
      Nat.pow_le_pow_left scalarBound _
    _ ≤ (32 * ScalarWindow.window (dyadicPrimes P) * Target.lambda n) ^ 3 := by gcongr; omega
    _ = 32 ^ 3 * (Target.lambda n) ^ 3 * ScalarWindow.window (dyadicPrimes P) ^ 3 := by ring
    _ ≤ 32 ^ 3 * (Target.lambda n) ^ 3 *
        ((16 ^ 3 * 48 ^ 4) * pairSide (ScalarWindow.window (dyadicPrimes P)) ^ 4) := Nat.mul_le_mul_left _ growth
    _ = _ := by ring

end NearQuarticWires.Cells.PrimeArithmetic
