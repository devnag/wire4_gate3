import Proof.Quartic.Cells.AsymptoticsPrime

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: a sufficiently
large prime scale pays the literal integer height guard of the rate chain. -/
theorem height_of_binary (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) (P : ℕ)
    (hP : 2 ^ (p.lambda / 4 + 1) ≤ P)
    (hpay : 2048 * (B1 + 80) * p.lambda ^ 2 ≤ 2 ^ (p.lambda / 4)) :
    64 * p.T ≤ (P / 4) / (2 * p.m) := by
  have ht := hs.T_upper B1 hb
  have hm := Nat.mul_le_mul_right ((B1 + 80) * p.lambda) hs.mu_le_lambda
  have htL : p.T ≤ (B1 + 80) * p.lambda ^ 2 := by nlinarith
  have hp : 2048 * p.T ≤ P := by
    calc
      2048 * p.T ≤ 2048 * ((B1 + 80) * p.lambda ^ 2) := Nat.mul_le_mul_left _ htL
      _ = 2048 * (B1 + 80) * p.lambda ^ 2 := by ring
      _ ≤ 2 ^ (p.lambda / 4) := hpay
      _ ≤ 2 ^ (p.lambda / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ P := hP
  apply (Nat.le_div_iff_mul_le (by rw [hs.m_eq]; norm_num : 0 < 2 * p.m)).mpr
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))).mpr
  rw [hs.m_eq]
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: uniformly over
all admitted public scale data, every prime scale above the proved binary
lower bound eventually satisfies the exact height guard. -/
theorem eventual_height (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ (x : ParameterInput) (p : Parameters) (P : ℕ), onset ≤ x.n → CoreRules x p →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 → 2 ^ (p.lambda / 4 + 1) ≤ P →
      64 * p.T ≤ (P / 4) / (2 * p.m) := by
  obtain ⟨onset, hon, hpay⟩ := NearCubicGates.Close.Counter.polynomial_lambda_binary (2048 * (B1 + 80)) 2
  refine ⟨onset, by omega, ?_⟩
  intro x p P hn hs hb hp
  apply hs.height_of_binary B1 hb P hp
  rw [hs.lambda_eq]
  exact (hpay x.n hn).2

end NearQuarticWires.Cells.CoreRules
