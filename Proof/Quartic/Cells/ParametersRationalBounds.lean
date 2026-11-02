import Proof.Quartic.Cells.ParametersScalarBounds
import Proof.Quartic.Cells.ParametersWordBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- All three rational fields of the literal parameter record have
polynomial bit length at the input precision, `sec:params` and
`prop:time`, paper/paper.tex. -/
theorem rational_preparation_bounds (hs : ParameterRules x p) (B1 L : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num.natAbs ≤ 2 ^ L) (hden : x.beta.den ≤ 2 ^ L) :
    let B := preparationEnvelope B1 x.n + L
    (p.pi0.num.natAbs ≤ 2 ^ B ∧ p.pi0.den ≤ 2 ^ B) ∧
      (p.eta.num.natAbs ≤ 2 ^ B ∧ p.eta.den ≤ 2 ^ B) ∧
      (p.ell0.num.natAbs ≤ 2 ^ B ∧ p.ell0.den ≤ 2 ^ B) := by
  have hc : CoreRules x p := hs
  have hscalar := hs.scalar_preparation_bounds B1 hb
  let V := preparationEnvelope B1 x.n
  have hv : V ≤ 2 ^ V := Nat.lt_two_pow_self.le
  have hpow : 2 ^ V ≤ 2 ^ (V + L) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  have hpowL : 2 ^ L ≤ 2 ^ (V + L) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  have hkpos : 0 < p.k := by
    rw [hs.k_eq]
    exact Nat.mul_pos (by have := hc.r_even_large.2; omega)
      (by rw [← hc.star_s]; exact hc.starParams.one_le_s)
  have htau : 0 < p.tau := by rw [hs.tau_eq]; omega
  have hU : 0 < p.U := by rw [hs.U_eq]; exact lt_of_lt_of_le htau (le_max_left ..)
  have hpi : p.pi0 = Rat.divInt (p.tau : ℤ) ((4 * p.U : ℕ) : ℤ) := by
    rw [hs.pi0_eq, Rat.divInt_eq_div]
    push_cast
    rfl
  have hpib := divInt_size_bounds (p.tau : ℤ) (4 * p.U) (by positivity)
  have hpiN : p.pi0.num.natAbs ≤ V := by
    rw [hpi]
    exact hpib.1.trans (by simpa only [Int.natAbs_natCast] using hscalar.tau)
  have hpiD : p.pi0.den ≤ V := by rw [hpi]; exact hpib.2.trans hscalar.pi0_denominator
  have heta : p.eta = x.beta / ((16 * p.MF : ℕ) : ℚ) := by
    rw [hs.eta_eq]
    push_cast
    rfl
  have hηb := div_natCast_size_bounds x.beta (16 * p.MF) (by have := hc.MF_pos; positivity)
  have hηN : p.eta.num.natAbs ≤ 2 ^ (V + L) := by
    rw [heta]
    exact hηb.1.trans (hnum.trans hpowL)
  have hηD : p.eta.den ≤ 2 ^ (V + L) := by
    rw [heta]
    calc
      (x.beta / ((16 * p.MF : ℕ) : ℚ)).den ≤ x.beta.den * (16 * p.MF) := hηb.2
      _ ≤ 2 ^ L * 2 ^ V := Nat.mul_le_mul hden (hscalar.eta_divisor.trans hv)
      _ = 2 ^ (V + L) := by rw [← pow_add, Nat.add_comm]
  have hell : p.ell0 = ((128 * p.U : ℕ) : ℚ) := by rw [hs.ell0_eq, hs.m_eq]
  have hellN : p.ell0.num.natAbs ≤ V := by
    rw [hell]
    simpa only [Rat.num_natCast, Int.natAbs_natCast] using hscalar.ell0_numerator
  have hellD : p.ell0.den ≤ 2 ^ (V + L) := by
    rw [hell, Rat.den_natCast]
    exact Nat.one_le_two_pow
  exact ⟨⟨hpiN.trans (hv.trans hpow), hpiD.trans (hv.trans hpow)⟩,
    ⟨hηN, hηD⟩, ⟨hellN.trans (hv.trans hpow), hellD⟩⟩

end NearQuarticWires.Cells.ParameterRules
