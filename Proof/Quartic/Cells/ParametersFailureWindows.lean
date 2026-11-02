import Proof.Quartic.Cells.ParametersPreparationTailBits
import Proof.Quartic.StagePrep.ChainWidths

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates NearCubicGates.Close.Counter

/-- `sec:params` and `prop:time`, paper/paper.tex: every scanned prime set, including the empty set
at zero, has a polynomial scalar window before any acceptance test. -/
theorem dyadicWindow_scan_bound (P : ℕ) :
    ScalarWindow.window (dyadicPrimes P) ≤ (P + 1) ^ 2 := by
  have hcard : (dyadicPrimes P).card ≤ P + 1 := by
    unfold dyadicPrimes
    exact (Finset.card_le_card (Finset.filter_subset ..)).trans (by rw [Finset.card_range])
  have hsum : ∑ q ∈ dyadicPrimes P, (q - 1) ≤ (P + 1) * P := by
    calc
      _ ≤ ∑ _q ∈ dyadicPrimes P, P := by
        apply Finset.sum_le_sum
        intro q hq
        have hqr : q < P + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
        omega
      _ = (dyadicPrimes P).card * P := by simp
      _ ≤ (P + 1) * P := Nat.mul_le_mul_right _ hcard
  unfold ScalarWindow.window
  nlinarith only [hsum, Nat.zero_le P]

/-- `sec:params` and `prop:time`, paper/paper.tex: clipping to the pair side never enlarges an
actual scalar window, even when a later rate-chain test fails. -/
theorem dyadicWindowInUse_scan_bound (P : ℕ) (pair : Bool) :
    windowInUse pair (pairSide (ScalarWindow.window (dyadicPrimes P)))
      (ScalarWindow.window (dyadicPrimes P)) ≤ (P + 1) ^ 2 := by
  have hD : 1 ≤ ScalarWindow.window (dyadicPrimes P) := by unfold ScalarWindow.window; omega
  have hpair : pairSide (ScalarWindow.window (dyadicPrimes P)) ≤ ScalarWindow.window (dyadicPrimes P) := by
    rcases pairSide_le_window (ScalarWindow.window (dyadicPrimes P)) with h | h
    · exact h
    · rw [h]
      exact hD
  unfold windowInUse
  split_ifs
  · exact hpair.trans (dyadicWindow_scan_bound P)
  · exact dyadicWindow_scan_bound P

/-- `sec:params` and `prop:time`, paper/paper.tex: both runtime windows fit the original-arity square
uniformly over every candidate of the finite prime scan. -/
theorem scan_windows_le_arity_square (n P : ℕ) (hP : P ≤ n) (pair : Bool) :
    ScalarWindow.window (dyadicPrimes P) ≤ (n + 1) ^ 2 ∧
      windowInUse pair (pairSide (ScalarWindow.window (dyadicPrimes P)))
        (ScalarWindow.window (dyadicPrimes P)) ≤ (n + 1) ^ 2 := by
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hP 1) 2
  exact ⟨(dyadicWindow_scan_bound P).trans hpow, (dyadicWindowInUse_scan_bound P pair).trans hpow⟩

/-- `imp:chain` and `prop:time`, paper/paper.tex: the final runtime product and index fit the rate-chain
word width on both successful and failed stopping outcomes. -/
theorem chain_finish_operand_bound (S D A i Lw Wd : ℕ)
    (hD : D < 2 ^ (5 * S + 22)) (hA : A ≤ D)
    (hi : i < 2 ^ S) (hLw : Lw < 2 ^ S) (hwidth : 6 * S + 40 ≤ Wd) :
    Lw * A + i + 8 < 2 ^ Wd := by
  have hprod := NearCubicGates.Close.Dispatch.lt_pow_mul hLw (hA.trans_lt hD)
  have hprod' : Lw * A < 2 ^ (6 * S + 22) := by
    simpa only [show S + (5 * S + 22) = 6 * S + 22 by omega] using hprod
  have hi' : i < 2 ^ (6 * S + 22) := hi.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h8 : 8 < 2 ^ (6 * S + 22) := (by norm_num : 8 < 2 ^ 4).trans_le
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsmall : Lw * A + i + 8 < 4 * 2 ^ (6 * S + 22) := by omega
  have heq : 4 * (2 : ℕ) ^ (6 * S + 22) = 2 ^ (6 * S + 24) := by
    rw [show 6 * S + 24 = (6 * S + 22) + 2 by omega, pow_add]
    norm_num
    ring
  rw [heq] at hsmall
  exact hsmall.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))

end NearQuarticWires.Cells.ParameterArithmetic
