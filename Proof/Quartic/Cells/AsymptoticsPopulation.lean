import Proof.Quartic.Cells.ParametersEventual

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and the proof of `thm:counter`, paper/paper.tex: either the chosen population scale equals the
precision floor, or its square is bounded directly by the wire population
term, with the integer ceiling paid by a factor of four. -/
theorem U_square_cases (hs : CoreRules x p) :
    p.U = p.tau ∨
      x.beta ^ 2 * (x.n : ℚ) ^ 3 * (p.U : ℚ) ^ 2 ≤
        4 * 96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2 := by
  by_cases heq : p.U = p.tau
  · exact Or.inl heq
  right
  have ht := ((hs.U_le_iff p.U).mp le_rfl).1
  have hta : 0 < p.tau := by
    rw [hs.tau_eq]
    have hk : 0 < p.k := by
      rw [hs.k_eq]
      have hr := hs.r_even_large.2
      have hspos : 1 ≤ p.s := by rw [← hs.star_s]; exact hs.starParams.one_le_s
      positivity
    omega
  have hU : 2 ≤ p.U := by omega
  have hroot : ((p.U - 1 : ℕ) : ℚ) ^ 2 <
      (96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2) /
        (x.beta ^ 2 * (x.n : ℚ) ^ 3) := by
    by_contra h
    have hle := (hs.U_le_iff (p.U - 1)).mpr ⟨by omega, le_of_not_gt h⟩
    omega
  have hden : 0 < x.beta ^ 2 * (x.n : ℚ) ^ 3 := by
    have := hs.beta_pos
    have : (0 : ℚ) < x.n := by exact_mod_cast hs.n_pos
    positivity
  have hpaid := (lt_div_iff₀ hden).mp hroot
  have hUlin : p.U ≤ 2 * (p.U - 1) := by omega
  have hUlinQ : (p.U : ℚ) ≤ 2 * ((p.U - 1 : ℕ) : ℚ) := by exact_mod_cast hUlin
  have hsquare := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ p.U) hUlinQ 2
  calc
    x.beta ^ 2 * (x.n : ℚ) ^ 3 * (p.U : ℚ) ^ 2 ≤
        x.beta ^ 2 * (x.n : ℚ) ^ 3 * (2 * ((p.U - 1 : ℕ) : ℚ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hden.le
    _ ≤ 4 * 96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2 := by nlinarith only [hpaid]

end NearQuarticWires.Cells.CoreRules
