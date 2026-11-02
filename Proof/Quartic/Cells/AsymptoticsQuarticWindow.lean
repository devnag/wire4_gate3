import Proof.Quartic.Cells.AsymptoticsCapArithmetic
import Proof.Quartic.Cells.AsymptoticsWindowCompletion

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- The fixed cost in the exact fourth-power form of the quartic
wire cap, `thm:counter`, paper/paper.tex. -/
def quarticCapCost (B1 : ℕ) : ℕ :=
  populationWindowCoefficient (primeScaleCoefficient B1) (B1 + 80)

namespace ParameterRules

/-- The full window condition under the exact fourth-power wire cap,
`thm:counter` and `eq:window`, paper/paper.tex. Both
integer-ceiling branches and both branches of the reference-length maximum
are included for the actual canonically selected parameters. -/
theorem eventual_fourth_power_window
    (B1 : ℕ) :
    ∃ onset : ℕ, 4 ≤ onset ∧ ∀ (x : ParameterInput) (p : Parameters),
      onset ≤ x.n → ParameterRules x p → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      (((quarticCapCost B1 : ℕ) : ℚ) * x.W) ^ 4 * (p.lambda : ℚ) ^ 17 * (p.mu : ℚ) ^ 30 <
        x.beta ^ 4 * (x.n : ℚ) ^ 16 →
      487 * (p.m : ℚ) * p.T * NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T / p.h <
        (p.Lw : ℚ) - 1 := by
  obtain ⟨og, hog, hg⟩ := eventual_window_geometry B1
  obtain ⟨op, hop, hp⟩ := eventual_prime_bounds B1
  obtain ⟨ofl, hofl, hfl⟩ := eventual_precision_window B1
  refine ⟨max og (max op ofl), by omega, ?_⟩
  intro x p hn hs hb hcap
  obtain ⟨hheight, hside, _, hgrowth, hwide⟩ := hg x p (by omega) hs hb
  apply hs.window_of_population hside ?_ hwide
  rcases CoreRules.U_square_cases (hs : CoreRules x p) with heq | hpop
  · rw [heq]
    exact hfl x p (by omega) hs hb hside
  · have hnpos : (0 : ℝ) < x.n := by exact_mod_cast hs.n_pos
    have hlogs := hs.logarithms_pos
    have hLpos : (0 : ℝ) < p.lambda := by exact_mod_cast (by omega : 0 < p.lambda)
    have hMpos : (0 : ℝ) < p.mu := by exact_mod_cast (by omega : 0 < p.mu)
    have hhpos : (0 : ℝ) < p.h := by
      have := hs.height
      have := hs.T_pos
      exact_mod_cast (by omega : 0 < p.h)
    have hspos : (0 : ℝ) < (p.L2 - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p.L2 - 1)
    have hbpos : (0 : ℝ) < x.beta := by exact_mod_cast hs.beta_pos
    have hWpos : (0 : ℝ) < x.W := by exact_mod_cast hs.input_valid.2.1
    have hprime : (x.n : ℝ) ≤
        (primeScaleCoefficient B1 : ℕ) * (p.lambda : ℝ) * (p.mu : ℝ) ^ 2 * p.P := by
      exact_mod_cast (hp x p (by omega) hs hb).2
    have hheightR : (p.P : ℝ) ≤ 64 * p.h := by exact_mod_cast hheight
    have hsideR : (p.P : ℝ) ^ 6 ≤
        (NearCubicGates.Close.Counter.pairGrowthConstant : ℕ) * (p.lambda : ℝ) ^ 3 *
          (2 * ((p.L2 - 1 : ℕ) : ℝ)) ^ 4 := by exact_mod_cast hgrowth
    have htime : (p.T : ℝ) ≤ ((B1 + 80 : ℕ) : ℝ) * p.lambda * p.mu := by
      have ht : p.T ≤ (B1 + 80) * p.lambda * p.mu := by
        nlinarith only [hs.T_upper B1 hb]
      exact_mod_cast ht
    have hpopR : (x.beta : ℝ) ^ 2 * (x.n : ℝ) ^ 3 * (p.U : ℝ) ^ 2 ≤
        4 * 96 ^ 2 * (16 * (p.mu : ℝ)) ^ 3 * (x.W : ℝ) ^ 2 := by
      rw [hs.r_eq] at hpop
      exact_mod_cast hpop
    have hcapR :
        (((populationWindowCoefficient (primeScaleCoefficient B1) (B1 + 80) : ℕ) : ℝ) * x.W) ^ 4 *
            (p.lambda : ℝ) ^ 17 * (p.mu : ℝ) ^ 30 < (x.beta : ℝ) ^ 4 * (x.n : ℝ) ^ 16 := by
      exact_mod_cast hcap
    have hresult := quartic_population_window (x.n : ℝ) p.lambda p.mu p.P p.h
      ((p.L2 - 1 : ℕ) : ℝ) p.T x.beta x.W p.U (primeScaleCoefficient B1) (B1 + 80)
      hnpos hLpos hMpos (by positivity) hhpos hspos (by positivity) hbpos hWpos (by positivity)
      (by unfold primeScaleCoefficient; positivity) (by omega)
      hprime hheightR hsideR htime hpopR hcapR
    exact_mod_cast hresult

end ParameterRules

end NearQuarticWires.Cells
