import Proof.Quartic.Cells.ParametersEventual

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `prop:complete`, paper/paper.tex: the integer
precision comparison implies the literal rational power side condition. -/
theorem k_precision_power (h : ceilLog 2 (16 / x.beta) ≤ p.k) :
    (16 : ℚ) / x.beta ≤ 2 ^ p.k := by
  exact_mod_cast (ceilLog_le_iff (by norm_num : 1 < 2) (16 / x.beta) p.k).mp h

/-- `prop:complete`, paper/paper.tex: the exact
population cap always satisfies the squared rational precision condition. -/
theorem Xmax_precision_power (hs : ParameterRules x p) :
    (2 : ℚ) ^ (2 * p.k) * (64 / x.beta) ^ 2 ≤ 2 ^ p.Xmax := by
  let L := ceilLog 2 (64 / x.beta)
  have hlog : (64 : ℚ) / x.beta ≤ 2 ^ L := by
    exact_mod_cast le_pow_ceilLog (by norm_num : 1 < 2) (64 / x.beta)
  have hnonneg : (0 : ℚ) ≤ 64 / x.beta := by have := hs.beta_pos; positivity
  calc
    (2 : ℚ) ^ (2 * p.k) * (64 / x.beta) ^ 2 ≤
        2 ^ (2 * p.k) * (2 ^ L) ^ 2 := by gcongr
    _ = 2 ^ (2 * p.k + 2 * L) := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ p.Xmax := pow_le_pow_right₀ (by norm_num) hs.Xmax_precision

end ParameterRules

/-- `lem:asymptotics` and `prop:complete`, paper/paper.tex: the actual selected parameters eventually satisfy
both power side conditions, uniformly over every admitted public input. -/
theorem eventual_prepare_precision (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x →
      1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      ∃ p, prepare x = some p ∧ ParameterRules x p ∧
        (16 : ℚ) / x.beta ≤ 2 ^ p.k ∧
        (2 : ℚ) ^ (2 * p.k) * (64 / x.beta) ^ 2 ≤ 2 ^ p.Xmax := by
  obtain ⟨os, hos, hs⟩ := eventual_prepare B1
  obtain ⟨ok, hok, hk⟩ := ParameterRules.eventual_k_precision B1
  refine ⟨max os ok, by omega, ?_⟩
  intro x hn hv hb
  obtain ⟨p, hp, hr⟩ := hs x (by omega) hv hb
  exact ⟨p, hp, hr, ParameterRules.k_precision_power (hk x p (by omega) hr hb),
    hr.Xmax_precision_power⟩

end NearQuarticWires.Cells
