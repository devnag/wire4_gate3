import Proof.Quartic.Cells.ParametersPublic

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: a uniform squared upper bound for the exact integer root. -/
theorem ceilSqrt_square_le (a : ℕ) : ceilSqrt a ^ 2 ≤ 4 * a + 4 := by
  have hu : ceilSqrt a ≤ Nat.sqrt a + 1 := by unfold ceilSqrt; split_ifs <;> omega
  have hsq := Nat.pow_le_pow_left hu 2
  have hr := Nat.sqrt_le' a
  have hs := Nat.sqrt_le_self a
  nlinarith

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the exact
integer population cap satisfies the natural squared scale bound. -/
theorem Xmax_square (hs : CoreRules x p) : p.Xmax ^ 2 ≤ 36 * p.tau ^ 2 * x.n * p.r + 4 := by
  have h := ceilSqrt_square_le (9 * p.tau ^ 2 * x.n * p.r)
  rw [← hs.Xmax_eq] at h
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: a polynomial
logarithmic bound on the square of the exact population cap. -/
theorem Xmax_polynomial_square (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.Xmax ^ 2 ≤ (600 * (B1 + 20) ^ 2) * p.lambda ^ 5 * x.n := by
  have ht := hs.tau_upper B1 hb
  have ht2 := Nat.pow_le_pow_left ht 2
  have hm3 := Nat.pow_le_pow_left hs.mu_le_lambda 3
  have hlogs := hs.logarithms_pos
  have hn := hs.n_pos
  calc
    p.Xmax ^ 2 ≤ 36 * p.tau ^ 2 * x.n * p.r + 4 := hs.Xmax_square
    _ ≤ 36 * ((B1 + 20) * p.mu * p.lambda) ^ 2 * x.n * (16 * p.mu) + 4 := by
      rw [hs.r_eq]
      gcongr
    _ = 576 * (B1 + 20) ^ 2 * p.mu ^ 3 * p.lambda ^ 2 * x.n + 4 := by ring
    _ ≤ 576 * (B1 + 20) ^ 2 * p.lambda ^ 5 * x.n + 4 := by
      have h := Nat.mul_le_mul_right (576 * (B1 + 20) ^ 2 * p.lambda ^ 2 * x.n) hm3
      nlinarith
    _ ≤ (600 * (B1 + 20) ^ 2) * p.lambda ^ 5 * x.n := by
      have hp : 0 < (B1 + 20) ^ 2 * p.lambda ^ 5 * x.n := by
        have hl : 0 < p.lambda := by omega
        positivity
      nlinarith

/-- `lem:asymptotics`, paper/paper.tex: the actual
mask-degree cost occupies at most half the concrete printing-degree trial. -/
theorem mask_degree_of_log (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hn : ((640000 : ℕ) ^ 2 * (600 * (B1 + 20) ^ 2) + 3000000) * p.lambda ^ 7 ≤ x.n) :
    2 * (4 * p.m * p.Xmax + 1) ≤ x.n / (10000 * p.lambda) := by
  have hX := hs.Xmax_polynomial_square B1 hb
  have hl := hs.logarithms_pos.1
  have hxmul := Nat.mul_le_mul_left ((640000 : ℕ) ^ 2 * p.lambda ^ 2) hX
  have hn := Nat.mul_le_mul_right x.n hn
  have hsq : (640000 * p.lambda * p.Xmax) ^ 2 ≤ x.n ^ 2 := by nlinarith
  have hlin : 640000 * p.lambda * p.Xmax ≤ x.n :=
    (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  have hp : p.lambda ≤ p.lambda ^ 7 := Nat.le_self_pow (by norm_num) _
  have hconst : 40000 * p.lambda ≤ x.n := by nlinarith
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 10000 * p.lambda)).mpr
  rw [hs.m_eq]
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: the combined
mask and moment degrees fit the concrete printing-degree trial. -/
theorem moment_degree_of_log (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hn : ((640000 : ℕ) ^ 2 * (600 * (B1 + 20) ^ 2) + 3000000) * p.lambda ^ 7 ≤ x.n) :
    4 * p.m * p.Xmax + 2 * p.m * p.k ≤ x.n / (10000 * p.lambda) := by
  have hmask := hs.mask_degree_of_log B1 hb hn
  have hl := hs.logarithms_pos.1
  have hk0 := hs.k_le
  have hmul := Nat.mul_le_mul_right (16 * p.lambda) hs.mu_le_lambda
  have hk : p.k ≤ 16 * p.lambda ^ 2 := by nlinarith
  have hpow : p.lambda ^ 3 ≤ p.lambda ^ 7 :=
    Nat.pow_le_pow_right (by omega) (by norm_num)
  have hhead : 4 * p.m * p.k ≤ x.n / (10000 * p.lambda) := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 10000 * p.lambda)).mpr
    rw [hs.m_eq]
    have hc : 2560000 * p.lambda ^ 3 ≤ x.n := by nlinarith
    have hkmul := Nat.mul_le_mul_right (160000 * p.lambda) hk
    nlinarith
  nlinarith

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `lem:asymptotics`, paper/paper.tex: uniformly over
all admitted calls, the computed mask and moment degree costs eventually fit
the explicit `n/lambda` printing-degree trial. -/
theorem eventual_publicScales_moment_degree (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      let p := publicScales x
      4 * p.m * p.Xmax + 2 * p.m * p.k ≤ x.n / (10000 * p.lambda) := by
  obtain ⟨oc, hoc, hc⟩ := eventual_publicScales_core
  obtain ⟨om, hom, hm⟩ := NearCubicGates.Close.Closure.lambda_poly_lt
    ((640000 : ℕ) ^ 2 * (600 * (B1 + 20) ^ 2) + 3000000) 7
  refine ⟨max oc om, by omega, ?_⟩
  intro x hn hv hb
  have hs := hc x (by omega) hv
  apply hs.moment_degree_of_log B1 hb
  rw [hs.lambda_eq]
  exact (hm x.n (by omega)).le

end NearQuarticWires.Cells
