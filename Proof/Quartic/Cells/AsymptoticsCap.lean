import Proof.Quartic.Cells.AsymptoticsQuarticWindow
import Proof.Quartic.Transfer.Counter4

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- Positivity of the fixed quartic cap cost, `thm:counter`,
paper/paper.tex. -/
theorem quarticCapCost_pos (B1 : ℕ) : 0 < quarticCapCost B1 := by
  unfold quarticCapCost populationWindowCoefficient
  omega

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- The fourth power of the paper's exact cap function, `thm:counter`,
paper/paper.tex: the fractional logarithmic exponents
become the integer powers `17` and `30` without a loss. -/
theorem A4_fourth (hs : ParameterRules x p) :
    (Transfer.A4 x.n) ^ 4 * (p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30 = (x.n : ℝ) ^ 16 := by
  have hlogs := hs.logarithms_pos
  have hL : (0 : ℝ) < p.lambda := by exact_mod_cast (by omega : 0 < p.lambda)
  have hM : (0 : ℝ) < p.mu := by exact_mod_cast (by omega : 0 < p.mu)
  have hLp : ((p.lambda : ℝ) ^ ((17 : ℝ) / 4)) ^ 4 = (p.lambda : ℝ) ^ 17 := by
    rw [← Real.rpow_mul_natCast hL.le]
    norm_num
  have hMp : ((p.mu : ℝ) ^ ((15 : ℝ) / 2)) ^ 4 = (p.mu : ℝ) ^ 30 := by
    rw [← Real.rpow_mul_natCast hM.le]
    norm_num
  unfold Transfer.A4
  rw [← hs.lambda_eq, ← hs.mu_eq]
  calc
    _ = (x.n : ℝ) ^ 16 / ((p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30) *
        ((p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30) := by
      rw [div_pow, mul_pow, hLp, hMp]
      ring
    _ = (x.n : ℝ) ^ 16 := div_mul_cancel₀ _ (by positivity)

/-- A fixed positive constant times the stated cap implies the strict
fourth-power comparison used by `eq:window`, `thm:counter`,
paper/paper.tex. -/
theorem fourth_power_cap (hs : ParameterRules x p) (B1 : ℕ)
    (hW : (x.W : ℝ) ≤ (1 / (2 * (quarticCapCost B1 : ℝ))) *
      (x.beta : ℝ) * Transfer.A4 x.n) :
    (((quarticCapCost B1 : ℕ) : ℚ) * x.W) ^ 4 * (p.lambda : ℚ) ^ 17 * (p.mu : ℚ) ^ 30 <
      x.beta ^ 4 * (x.n : ℚ) ^ 16 := by
  have hC : (0 : ℝ) < quarticCapCost B1 := by exact_mod_cast quarticCapCost_pos B1
  have hb : (0 : ℝ) < x.beta := by exact_mod_cast hs.beta_pos
  have hn : (0 : ℝ) < x.n := by exact_mod_cast hs.n_pos
  have hCW : (quarticCapCost B1 : ℝ) * x.W ≤ (x.beta : ℝ) * Transfer.A4 x.n / 2 := by
    calc
      _ ≤ (quarticCapCost B1 : ℝ) *
          ((1 / (2 * (quarticCapCost B1 : ℝ))) * (x.beta : ℝ) * Transfer.A4 x.n) :=
        mul_le_mul_of_nonneg_left hW hC.le
      _ = _ := by field_simp
  have hpow := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ (quarticCapCost B1 : ℝ) * x.W) hCW 4
  have hreal :
      ((quarticCapCost B1 : ℝ) * x.W) ^ 4 * (p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30 <
        (x.beta : ℝ) ^ 4 * (x.n : ℝ) ^ 16 := by
    calc
      _ ≤ ((x.beta : ℝ) * Transfer.A4 x.n / 2) ^ 4 *
          (p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30 := by gcongr
      _ = (x.beta : ℝ) ^ 4 / 16 *
          ((Transfer.A4 x.n) ^ 4 * (p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30) := by ring
      _ = (x.beta : ℝ) ^ 4 * (x.n : ℝ) ^ 16 / 16 := by rw [hs.A4_fourth]; ring
      _ < _ := div_lt_self (by positivity) (by norm_num : (1 : ℝ) < 16)
  exact_mod_cast hreal

end ParameterRules

/-- `lem:asymptotics`, `prop:complete`, and the quartic cap of
`thm:counter`, paper/paper.tex: one positive
constant and one onset uniformly supply the actual selected parameters,
both literal precision side conditions, and the full window inequality
under the stated `beta A4(n)` wire cap. -/
theorem eventual_quartic_cap
    (B1 : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∃ onset : ℕ, 4 ≤ onset ∧
      ∀ x : ParameterInput, onset ≤ x.n → ValidInput x → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
        (x.W : ℝ) ≤ a * (x.beta : ℝ) * Transfer.A4 x.n →
        ∃ p, prepare x = some p ∧ ParameterRules x p ∧
          (16 : ℚ) / x.beta ≤ 2 ^ p.k ∧
          (2 : ℚ) ^ (2 * p.k) * (64 / x.beta) ^ 2 ≤ 2 ^ p.Xmax ∧
          487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h <
            (p.Lw : ℚ) - 1 := by
  obtain ⟨os, hos, hs⟩ := eventual_prepare_precision B1
  obtain ⟨ow, how, hw⟩ := ParameterRules.eventual_fourth_power_window B1
  refine ⟨1 / (2 * (quarticCapCost B1 : ℝ)), by have := quarticCapCost_pos B1; positivity,
    max os ow, by omega, ?_⟩
  intro x hn hv hb hW
  obtain ⟨p, hp, hr, hk, hX⟩ := hs x (by omega) hv hb
  exact ⟨p, hp, hr, hk, hX, hw x p (by omega) hr hb (hr.fourth_power_cap B1 hW)⟩

end NearQuarticWires.Cells
