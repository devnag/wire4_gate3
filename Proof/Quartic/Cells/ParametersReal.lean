import Proof.Quartic.Cells.ParametersBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `sec:params`, paper/paper.tex: the square of the
population expression is the rational value used by exact selection. -/
theorem population_square (n r W : ℕ) (beta : ℚ) :
    ((96 : ℝ) * (r : ℝ) ^ ((3 : ℝ) / 2) * W /
      ((beta : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2))) ^ 2 =
        (((96 ^ 2 * (r : ℚ) ^ 3 * (W : ℚ) ^ 2) /
          (beta ^ 2 * (n : ℚ) ^ 3) : ℚ) : ℝ) := by
  have hr : ((r : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (r : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hn : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  push_cast
  simp only [div_pow, mul_pow, hr, hn]

/-- `sec:params`, paper/paper.tex: raising the sample
threshold to the fourth power preserves and reflects its inequality. -/
theorem fourthRoot_budget_iff {C X Q eta : ℝ}
    (hC : 0 ≤ C) (hX : 0 ≤ X) (hQ : 0 ≤ Q) (he : 0 < eta) :
    C / eta ^ 2 * X ^ ((4 : ℝ)⁻¹) ≤ Q ↔ C ^ 4 * X ≤ Q ^ 4 * eta ^ 8 := by
  have hr : (X ^ ((4 : ℝ)⁻¹)) ^ 4 = X :=
    Real.rpow_inv_natCast_pow hX (by norm_num : (4 : ℕ) ≠ 0)
  have hA : 0 ≤ C / eta ^ 2 * X ^ ((4 : ℝ)⁻¹) := by positivity
  have he8 : 0 < eta ^ 8 := pow_pos he _
  have heq : (C / eta ^ 2 * X ^ ((4 : ℝ)⁻¹)) ^ 4 * eta ^ 8 = C ^ 4 * X := by
    rw [mul_pow, hr]
    field_simp
  constructor
  · intro h
    have h4 := pow_le_pow_left₀ hA h 4
    have hm := mul_le_mul_of_nonneg_right h4 he8.le
    rwa [heq] at hm
  · intro h
    rw [← heq] at h
    have h4 : (C / eta ^ 2 * X ^ ((4 : ℝ)⁻¹)) ^ 4 ≤ Q ^ 4 := by
      nlinarith
    exact (pow_le_pow_iff_left₀ hA hQ (by norm_num : (4 : ℕ) ≠ 0)).mp h4

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the exact rational
implementation selects precisely the least integer above the printed population
expression and the lower bound `tau`. -/
theorem U_real_le_iff (hs : CoreRules x p) (t : ℕ) :
    p.U ≤ t ↔ p.tau ≤ t ∧
      (96 : ℝ) * (p.r : ℝ) ^ ((3 : ℝ) / 2) * x.W /
        ((x.beta : ℝ) * (x.n : ℝ) ^ ((3 : ℝ) / 2)) ≤ t := by
  let V : ℝ := (96 : ℝ) * (p.r : ℝ) ^ ((3 : ℝ) / 2) * x.W /
    ((x.beta : ℝ) * (x.n : ℝ) ^ ((3 : ℝ) / 2))
  have hV : 0 ≤ V := by
    dsimp [V]
    have hb : 0 < (x.beta : ℝ) := by exact_mod_cast hs.beta_pos
    positivity
  have heq := population_square x.n p.r x.W x.beta
  change V ^ 2 = _ at heq
  rw [hs.U_le_iff]
  constructor
  · rintro ⟨ht, hq⟩
    refine ⟨ht, ?_⟩
    have hqr : (((96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2) /
      (x.beta ^ 2 * (x.n : ℚ) ^ 3) : ℚ) : ℝ) ≤ (t : ℝ) ^ 2 := by exact_mod_cast hq
    rw [← heq] at hqr
    change V ≤ t
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  · rintro ⟨ht, hVt⟩
    refine ⟨ht, ?_⟩
    have hqr : V ^ 2 ≤ (t : ℝ) ^ 2 := by
      change V ≤ t at hVt
      nlinarith [Nat.cast_nonneg (α := ℝ) t]
    rw [heq] at hqr
    exact_mod_cast hqr

/-- `sec:params`, paper/paper.tex: the dyadic exponent
selected by the exact fourth-power comparison is least for the original real
fourth-root sample threshold. -/
theorem Qexp_real_le_iff (hs : CoreRules x p) (q : ℕ) :
    p.Qexp ≤ q ↔
      ((1024 * p.N * p.m : ℕ) : ℝ) / (p.eta : ℝ) ^ 2 *
        ((4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) : ℝ) ^ ((4 : ℝ)⁻¹) ≤
          ((2 ^ q : ℕ) : ℝ) := by
  have he : 0 < (p.eta : ℝ) := by exact_mod_cast hs.eta_pos
  rw [fourthRoot_budget_iff (by positivity) (by positivity) (by positivity) he]
  have hr := hs.Qexp_le_iff q
  constructor
  · intro h
    exact_mod_cast hr.mp h
  · intro h
    apply hr.mpr
    exact_mod_cast h

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the exact rational
implementation selects precisely the least integer above the printed population
expression and the lower bound `tau`. -/
theorem U_real_le_iff (hs : ParameterRules x p) (t : ℕ) :
    p.U ≤ t ↔ p.tau ≤ t ∧
      (96 : ℝ) * (p.r : ℝ) ^ ((3 : ℝ) / 2) * x.W /
        ((x.beta : ℝ) * (x.n : ℝ) ^ ((3 : ℝ) / 2)) ≤ t :=
  CoreRules.U_real_le_iff (hs : CoreRules x p) t

/-- `sec:params`, paper/paper.tex: the dyadic exponent
selected by the exact fourth-power comparison is least for the original real
fourth-root sample threshold. -/
theorem Qexp_real_le_iff (hs : ParameterRules x p) (q : ℕ) :
    p.Qexp ≤ q ↔
      ((1024 * p.N * p.m : ℕ) : ℝ) / (p.eta : ℝ) ^ 2 *
        ((4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)) : ℕ) : ℝ) ^ ((4 : ℝ)⁻¹) ≤
          ((2 ^ q : ℕ) : ℝ) :=
  CoreRules.Qexp_real_le_iff (hs : CoreRules x p) q

end NearQuarticWires.Cells.ParameterRules

