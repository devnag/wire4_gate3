import Proof.Quartic.Cells.AsymptoticsSample
import Proof.Quartic.Cells.ParametersGuards

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: the actual
common numerator exponent has an exact linear formula in the seed, inner
dimension and dyadic sample exponent. -/
theorem BN_formula (hs : CoreRules x p) : p.BN = p.S + 12 * p.k + 8 * p.Qexp + 1 := by
  have hp : p.N ^ 2 * p.Q = 2 ^ (p.k + p.Qexp) := by
    rw [hs.N_square, hs.Q_eq, ← pow_add]
  rw [hs.BN_eq, hp, Nat.clog_pow 2 _ (by norm_num), hs.m_eq]
  ring

/-- `lem:asymptotics`, paper/paper.tex: the exact
common numerator exponent is at least twenty times the inner dimension. -/
theorem BN_lower (hs : CoreRules x p) : 20 * p.k + 1 ≤ p.BN := by
  have he : p.k ≤ p.ellf := by rw [hs.ellf_eq]; exact le_max_left _ _
  rw [hs.BN_formula, hs.S_eq, hs.m_eq]
  omega

/-- `lem:asymptotics`, paper/paper.tex: the actual
common numerator exponent is uniformly at most a constant times `mu lambda`. -/
theorem BN_upper (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.BN ≤ (32 * B1 + 2200) * p.mu * p.lambda := by
  have hq := hs.Qexp_four_upper B1 hb
  have hk := hs.k_le
  have hlogs := hs.logarithms_pos
  have hS : p.S ≤ 8 * (p.k + p.Qexp + 1) := by
    rw [hs.S_eq, hs.m_eq, hs.ellf_eq]
    omega
  have hm := Nat.mul_le_mul_left (16 * (2 * B1 + 100))
    (Nat.mul_le_mul_right p.lambda hlogs.2)
  rw [hs.BN_formula]
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: every sufficiently
large trial prime scale admits a positive lift exponent of order `mu`. -/
theorem lift_trial (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) (P : ℕ)
    (hP : 2 ^ (p.lambda / 4 + 1) ≤ P) (hL : 16 ≤ p.lambda) :
    LiftPass p.BN P (8 * (32 * B1 + 2200) * p.mu) := by
  have hmu := hs.logarithms_pos.2
  have hBN := hs.BN_upper B1 hb
  have hquot : p.lambda ≤ 8 * (p.lambda / 4) := by omega
  have hm := Nat.mul_le_mul_left ((32 * B1 + 2200) * p.mu) hquot
  have hbnd : p.BN ≤ (p.lambda / 4) * (8 * (32 * B1 + 2200) * p.mu) := by nlinarith
  refine ⟨by nlinarith, ?_⟩
  calc
    2 ^ (p.BN + 8 * (32 * B1 + 2200) * p.mu) ≤
        2 ^ ((p.lambda / 4 + 1) * (8 * (32 * B1 + 2200) * p.mu)) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ = (2 ^ (p.lambda / 4 + 1)) ^ (8 * (32 * B1 + 2200) * p.mu) := pow_mul _ _ _
    _ ≤ P ^ (8 * (32 * B1 + 2200) * p.mu) := Nat.pow_le_pow_left hP _

/-- `lem:asymptotics`, paper/paper.tex: the actual
least lift search succeeds and returns an exponent bounded by the trial one. -/
theorem liftExponent_le_trial (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) (P : ℕ)
    (hP : 2 ^ (p.lambda / 4 + 1) ≤ P) (hL : 16 ≤ p.lambda) :
    ∃ e, liftExponent p.BN P = some e ∧ 1 ≤ e ∧ e ≤ 8 * (32 * B1 + 2200) * p.mu := by
  have hP4 : 4 ≤ P := by
    calc
      4 = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ 2 ^ (p.lambda / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ P := hP
  obtain ⟨e, he⟩ := liftExponent_isSome p.BN P hP4
  have hsel := liftExponent_spec p.BN P e he
  have htrial := hs.lift_trial B1 hb P hP hL
  refine ⟨e, he, hsel.1.1, ?_⟩
  by_contra hn
  exact hsel.2.2 _ (by omega) htrial

/-- `lem:asymptotics`, paper/paper.tex: every passing
lift below the input length pays the numerator exponent in binary degree. -/
theorem lift_lower (hs : CoreRules x p) (P e : ℕ) (hP : P ≤ x.n) (he : LiftPass p.BN P e) :
    20 * p.k ≤ p.lambda * e := by
  have hn : x.n ≤ 2 ^ p.lambda := by
    rw [hs.lambda_eq]
    exact Nat.le_pow_clog (by norm_num) _
  have hp : 2 ^ (p.BN + e) ≤ 2 ^ (p.lambda * e) := by
    calc
      2 ^ (p.BN + e) ≤ P ^ e := he.2
      _ ≤ (2 ^ p.lambda) ^ e := Nat.pow_le_pow_left (hP.trans hn) _
      _ = 2 ^ (p.lambda * e) := (pow_mul _ _ _).symm
  have hpow := (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hp
  have hBN := hs.BN_lower
  omega

end NearQuarticWires.Cells.CoreRules
