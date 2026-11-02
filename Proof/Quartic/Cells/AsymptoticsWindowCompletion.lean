import Proof.Quartic.Cells.AsymptoticsWindow
import Proof.Quartic.Cells.AsymptoticsPopulation

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- The precision-floor branch of the cap proof, `thm:counter`,
paper/paper.tex: the exact `T tau` cost is eventually
smaller than the actual pair-window height product. -/
theorem eventual_precision_window (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → ParameterRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → 2 ≤ p.L2 →
      249344 * p.T * p.tau < p.h * (p.L2 - 1) := by
  obtain ⟨op, hop, hp⟩ := eventual_prime_bounds B1
  obtain ⟨ol, hol, hl⟩ := NearCubicGates.Close.Counter.polynomial_lambda_binary
    (128 * 249344 * (B1 + 80) * (B1 + 20)) 4
  refine ⟨max op ol, by omega, ?_⟩
  intro x p hn hs hb hside
  have ht := hs.T_upper B1 hb
  have hτ := hs.tau_upper B1 hb
  have hm := hs.mu_le_lambda
  have hcost : 249344 * p.T * p.tau ≤
      249344 * (B1 + 80) * (B1 + 20) * p.lambda ^ 4 := by
    calc
      _ ≤ 249344 * ((B1 + 80) * p.mu * p.lambda) *
          ((B1 + 20) * p.mu * p.lambda) := by gcongr
      _ ≤ 249344 * ((B1 + 80) * p.lambda * p.lambda) *
          ((B1 + 20) * p.lambda * p.lambda) := by gcongr
      _ = _ := by ring
  have hpaid : 128 * (249344 * (B1 + 80) * (B1 + 20) * p.lambda ^ 4) ≤ p.P := by
    calc
      _ = 128 * 249344 * (B1 + 80) * (B1 + 20) *
          (NearCubicGates.Target.lambda x.n) ^ 4 := by rw [hs.lambda_eq]; ring
      _ ≤ 2 ^ (NearCubicGates.Target.lambda x.n / 4) := (hl x.n (by omega)).2
      _ = 2 ^ (p.lambda / 4) := by rw [hs.lambda_eq]
      _ ≤ 2 ^ (p.lambda / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p.P := (hp x p (by omega) hs hb).1
  have hheight := hs.height_scale.2
  have hpos : 0 < p.h := by have := hs.height; have := hs.T_pos; omega
  have hstrict : 249344 * p.T * p.tau < p.h := by omega
  exact hstrict.trans_le (Nat.le_mul_of_pos_right _ (by omega))

/-- `eq:window`, paper/paper.tex:
the two exact integer branch comparisons imply the full rational window
inequality with the original maximum reference length. -/
theorem window_of_population (hs : ParameterRules x p)
    (hside : 2 ≤ p.L2)
    (hpop : 249344 * p.T * p.U < p.h * (p.L2 - 1))
    (hwide : 487 * p.m * p.h < 256 * (p.Lw - 1)) :
    487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h <
      (p.Lw : ℚ) - 1 := by
  have hLw := hs.window_bounds.2.2
  have hLwpos : 1 ≤ p.Lw := by omega
  have hh : (0 : ℚ) < p.h := by
    have ht := hs.T_pos
    have h := hs.height
    exact_mod_cast (by omega : 0 < p.h)
  have ht : (0 : ℚ) < p.T := by exact_mod_cast hs.T_pos
  have hpopq : (249344 : ℚ) * p.T * p.U < (p.h : ℚ) * (p.L2 - 1 : ℕ) := by
    exact_mod_cast hpop
  have hsideq : ((p.L2 - 1 : ℕ) : ℚ) ≤ (p.Lw : ℚ) - 1 := by
    have hcast : (p.L2 : ℚ) ≤ p.Lw := by exact_mod_cast hLw
    rw [Nat.cast_sub (by omega : 1 ≤ p.L2), Nat.cast_one]
    linarith
  have hlinear : 487 * (p.m : ℚ) * p.T * p.ell0 / p.h < (p.Lw : ℚ) - 1 := by
    apply (div_lt_iff₀ hh).mpr
    rw [hs.ell0_eq, hs.m_eq]
    push_cast
    calc
      487 * 4 * (p.T : ℚ) * (128 * p.U) = 249344 * p.T * p.U := by ring
      _ < (p.h : ℚ) * (p.L2 - 1 : ℕ) := hpopq
      _ ≤ (p.h : ℚ) * ((p.Lw : ℚ) - 1) := mul_le_mul_of_nonneg_left hsideq hh.le
      _ = ((p.Lw : ℚ) - 1) * p.h := by ring
  have hwideq : (487 : ℚ) * p.m * p.h < 256 * ((p.Lw : ℚ) - 1) := by
    have hq : (487 : ℚ) * p.m * p.h < 256 * ((p.Lw - 1 : ℕ) : ℚ) := by exact_mod_cast hwide
    simpa only [Nat.cast_sub hLwpos, Nat.cast_one] using hq
  have hquadratic :
      487 * (p.m : ℚ) * p.T * ((p.h : ℚ) ^ 2 / (256 * p.T)) / p.h < (p.Lw : ℚ) - 1 := by
    calc
      _ = 487 * (p.m : ℚ) * p.h / 256 := by field_simp
      _ < _ := (div_lt_iff₀ (by norm_num : (0 : ℚ) < 256)).mpr (by linarith only [hwideq])
  unfold NearCubicGates.Close.Counter.ellBar
  rcases le_total p.ell0 ((p.h : ℚ) ^ 2 / (256 * p.T)) with h | h
  · rw [max_eq_right h]
    exact hquadratic
  · rw [max_eq_left h]
    exact hlinear

end NearQuarticWires.Cells.ParameterRules
