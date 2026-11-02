import Proof.Quartic.Cells.AsymptoticsRuntime
import Proof.Quartic.Cells.AsymptoticsNumerator

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the exact
concentration test forces the stated lower scale for `T`. -/
theorem T_lower (hs : CoreRules x p) : 4 * p.k ≤ p.T := by
  have htest := ((hs.T_le_iff p.T).mp le_rfl).2
  have hb : x.beta ≤ 1 := by have := hs.input_valid.2.2.2.2.2.1; linarith
  have hnat : 2 ^ (p.m * p.k + 2 * p.m + 5) * p.Jmax ≤ 2 ^ p.T := by
    have hscale := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℚ) ≤ 2 ^ p.T)
    have hr : ((2 ^ (p.m * p.k + 2 * p.m + 5) * p.Jmax : ℕ) : ℚ) ≤ 2 ^ p.T := by
      nlinarith only [htest, hscale]
    exact_mod_cast hr
  have hj : 0 < p.Jmax := by rw [hs.Jmax_eq]; omega
  have hpow : 2 ^ (p.m * p.k) ≤ 2 ^ p.T := by
    calc
      _ ≤ 2 ^ (p.m * p.k + 2 * p.m + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ (p.m * p.k + 2 * p.m + 5) * p.Jmax := Nat.le_mul_of_pos_right _ hj
      _ ≤ _ := hnat
  have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow
  rwa [hs.m_eq] at h

/-- `lem:asymptotics`, paper/paper.tex: the precision
scale is at least the actual inner dimension. -/
theorem tau_lower (hs : CoreRules x p) : p.k ≤ p.tau := by rw [hs.tau_eq]; omega

/-- `lem:asymptotics`, paper/paper.tex: the sharp
upper population-cap scale retains all three powers of `mu` after squaring. -/
theorem Xmax_square_sharp_upper (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.Xmax ^ 2 ≤ 600 * (B1 + 20) ^ 2 * p.lambda ^ 2 * p.mu ^ 3 * x.n := by
  have ht := hs.tau_upper B1 hb
  have hlogs := hs.logarithms_pos
  have hn := hs.n_pos
  calc
    p.Xmax ^ 2 ≤ 36 * p.tau ^ 2 * x.n * p.r + 4 := hs.Xmax_square
    _ ≤ 36 * ((B1 + 20) * p.mu * p.lambda) ^ 2 * x.n * (16 * p.mu) + 4 := by
      rw [hs.r_eq]
      gcongr
    _ = 576 * (B1 + 20) ^ 2 * p.lambda ^ 2 * p.mu ^ 3 * x.n + 4 := by ring
    _ ≤ _ := by
      have hpos : 0 < (B1 + 20) ^ 2 * p.lambda ^ 2 * p.mu ^ 3 * x.n := by
        have hl : 0 < p.lambda := by omega
        have hm : 0 < p.mu := by omega
        positivity
      nlinarith only [hpos]

/-- `lem:asymptotics`, paper/paper.tex: the matching
lower squared population-cap scale follows from the actual integer root. -/
theorem Xmax_square_sharp_lower (hs : CoreRules x p) (hk : 8 * p.mu * p.lambda ≤ p.k) :
    9216 * p.lambda ^ 2 * p.mu ^ 3 * x.n ≤ p.Xmax ^ 2 := by
  have ht := hk.trans hs.tau_lower
  calc
    _ = 9 * (8 * p.mu * p.lambda) ^ 2 * x.n * (16 * p.mu) := by ring
    _ ≤ 9 * p.tau ^ 2 * x.n * p.r := by rw [hs.r_eq]; gcongr
    _ ≤ p.Xmax ^ 2 := (hs.Xmax_le_iff p.Xmax).mp le_rfl

/-- The first six scales in `lem:asymptotics`, paper/paper.tex, as uniform two-sided integer comparisons for the actual public
parameters, including the sharp squared scale of `Xmax`. -/
theorem eventual_shape_scales (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      (8 * p.mu * p.lambda ≤ p.k ∧ p.k ≤ 16 * p.mu * p.lambda) ∧
      (32 * p.mu * p.lambda ≤ p.T ∧ p.T ≤ (B1 + 80) * p.mu * p.lambda) ∧
      (8 * p.mu * p.lambda ≤ p.tau ∧ p.tau ≤ (B1 + 20) * p.mu * p.lambda) ∧
      (9216 * p.lambda ^ 2 * p.mu ^ 3 * x.n ≤ p.Xmax ^ 2 ∧
        p.Xmax ^ 2 ≤ 600 * (B1 + 20) ^ 2 * p.lambda ^ 2 * p.mu ^ 3 * x.n) ∧
      (160 * p.mu * p.lambda ≤ p.BN ∧ p.BN ≤ (32 * B1 + 2200) * p.mu * p.lambda) := by
  obtain ⟨onset, hon, hk⟩ := eventual_k_bounds
  refine ⟨onset, hon, ?_⟩
  intro x p hn hs hb
  obtain ⟨hklo, hkup⟩ := hk x p hn hs
  have hT := hs.T_lower
  have hBN := hs.BN_lower
  exact ⟨⟨hklo, hkup⟩, ⟨by nlinarith only [hT, hklo], hs.T_upper B1 hb⟩,
    ⟨hklo.trans hs.tau_lower, hs.tau_upper B1 hb⟩,
    ⟨hs.Xmax_square_sharp_lower hklo, hs.Xmax_square_sharp_upper B1 hb⟩,
    ⟨by nlinarith only [hBN, hklo], hs.BN_upper B1 hb⟩⟩

end NearQuarticWires.Cells.CoreRules
