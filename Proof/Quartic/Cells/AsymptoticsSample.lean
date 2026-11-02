import Proof.Quartic.Cells.AsymptoticsPrecision

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: both actual
Fourier periods are bounded by `33 n⁴`. -/
theorem omega_upper (hs : CoreRules x p) :
    p.omega1 ≤ 33 * x.n ^ 4 ∧ p.omega2 ≤ 33 * x.n ^ 4 := by
  have hG := hs.input_valid.2.2.1
  have hW := hs.input_valid.2.2.2.1
  have hn := hs.n_pos
  have hn4 : 0 < x.n ^ 4 := by positivity
  rw [hs.omega1_eq, hs.omega2_eq, hs.m_eq]
  constructor <;> nlinarith

/-- `lem:asymptotics`, paper/paper.tex: the actual
Fourier mass envelope is bounded by `33 n⁴`. -/
theorem MF_upper (hs : CoreRules x p) : p.MF ≤ 33 * x.n ^ 4 := by
  apply (hs.MF_le_iff _).mpr
  have h := Nat.mul_le_mul hs.omega_upper.1 hs.omega_upper.2
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: the sampler
tolerance is bounded below by an explicit polynomial scale independent of
the denominator used to encode the precision. -/
theorem eta_scale_lower (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    1 ≤ p.eta * ((528 * x.n ^ (B1 + 4) : ℕ) : ℚ) := by
  have hMF : (p.MF : ℚ) ≤ 33 * (x.n : ℚ) ^ 4 := by exact_mod_cast hs.MF_upper
  have hden : 0 < (16 * p.MF : ℚ) := by have := hs.MF_pos; positivity
  rw [hs.eta_eq, div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  push_cast
  calc
    1 * (16 * (p.MF : ℚ)) ≤ 528 * (x.n : ℚ) ^ 4 := by nlinarith
    _ ≤ 528 * (x.n : ℚ) ^ 4 * (x.beta * (x.n : ℚ) ^ B1) := by
      have h := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (528 : ℚ) * (x.n : ℚ) ^ 4)
      simpa using h
    _ = x.beta * (528 * (x.n : ℚ) ^ (B1 + 4)) := by rw [pow_add]; ring

/-- `lem:asymptotics`, paper/paper.tex: the sixth power
of the actual matrix side is bounded by the exact inner-dimension exponent. -/
theorem N_sixth (hs : CoreRules x p) : p.N ^ 6 ≤ 2 ^ (3 * p.k) := by
  rw [hs.N_eq, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- `lem:asymptotics`, paper/paper.tex: the literal
fourth-power sample numerator, multiplied by the eighth power of the tolerance
scale, has the required binary upper bound. -/
theorem sample_scaled_binary (hs : CoreRules x p) (B1 : ℕ) :
    ((1024 * p.N * p.m) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)))) *
      (528 * x.n ^ (B1 + 4)) ^ 8 ≤
        2 ^ (143 + 3 * p.k + (8 * B1 + 40) * p.lambda) := by
  have ht : p.omega1 * p.omega2 ≤ (33 * x.n ^ 4) ^ 2 := by
    have h := Nat.mul_le_mul hs.omega_upper.1 hs.omega_upper.2
    nlinarith
  have hn : x.n ≤ 2 ^ p.lambda := by
    rw [hs.lambda_eq]
    exact Nat.le_pow_clog (by norm_num) _
  have heq : (1024 * p.N * p.m) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2))) =
      2 ^ 51 * p.N ^ 6 * (p.omega1 * p.omega2) := by
    rw [hs.m_eq]
    norm_num only [Nat.reducePow]
    ring
  have hsq : (33 * x.n ^ 4) ^ 2 = 33 ^ 2 * x.n ^ 8 := by ring
  have hd : (528 * x.n ^ (B1 + 4)) ^ 8 = 528 ^ 8 * x.n ^ ((B1 + 4) * 8) := by
    rw [mul_pow, ← pow_mul]
  have hj : x.n ^ 8 * x.n ^ ((B1 + 4) * 8) = x.n ^ (8 * B1 + 40) := by
    rw [← pow_add]
    congr 1
    ring
  have hc : (2 : ℕ) ^ 51 * 33 ^ 2 * 528 ^ 8 ≤ 2 ^ 143 := by norm_num
  have hnp : x.n ^ (8 * B1 + 40) ≤ 2 ^ ((8 * B1 + 40) * p.lambda) := by
    calc
      x.n ^ (8 * B1 + 40) ≤ (2 ^ p.lambda) ^ (8 * B1 + 40) := Nat.pow_le_pow_left hn _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  calc
    ((1024 * p.N * p.m) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)))) *
        (528 * x.n ^ (B1 + 4)) ^ 8 =
          (2 ^ 51 * p.N ^ 6 * (p.omega1 * p.omega2)) * (528 * x.n ^ (B1 + 4)) ^ 8 := by rw [heq]
    _ ≤ (2 ^ 51 * p.N ^ 6 * (33 * x.n ^ 4) ^ 2) * (528 * x.n ^ (B1 + 4)) ^ 8 := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ht)
    _ = (2 ^ 51 * 33 ^ 2 * 528 ^ 8) * p.N ^ 6 *
        (x.n ^ 8 * x.n ^ ((B1 + 4) * 8)) := by rw [hsq, hd]; ring
    _ = (2 ^ 51 * 33 ^ 2 * 528 ^ 8) * p.N ^ 6 * x.n ^ (8 * B1 + 40) := by rw [hj]
    _ ≤ 2 ^ 143 * 2 ^ (3 * p.k) * 2 ^ ((8 * B1 + 40) * p.lambda) :=
      Nat.mul_le_mul (Nat.mul_le_mul hc hs.N_sixth) hnp
    _ = 2 ^ (143 + 3 * p.k + (8 * B1 + 40) * p.lambda) := by rw [← pow_add, ← pow_add]

/-- `lem:asymptotics`, paper/paper.tex: the actual least
dyadic sampler size has coefficient three quarters in the inner dimension. -/
theorem Qexp_upper (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.Qexp ≤ (3 * p.k) / 4 + (2 * B1 + 100) * p.lambda := by
  let q := (3 * p.k) / 4 + (2 * B1 + 100) * p.lambda
  let A := (1024 * p.N * p.m) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)))
  let D := 528 * x.n ^ (B1 + 4)
  have he : 143 + 3 * p.k + (8 * B1 + 40) * p.lambda ≤ 4 * q := by
    have hr := Nat.mod_lt (3 * p.k) (by norm_num : 0 < (4 : ℕ))
    have hd := Nat.mod_add_div (3 * p.k) 4
    have hl := hs.logarithms_pos.1
    dsimp [q]
    nlinarith
  have hn : A * D ^ 8 ≤ (2 ^ q) ^ 4 := by
    calc
      A * D ^ 8 ≤ 2 ^ (143 + 3 * p.k + (8 * B1 + 40) * p.lambda) := hs.sample_scaled_binary B1
      _ ≤ 2 ^ (4 * q) := Nat.pow_le_pow_right (by norm_num) he
      _ = (2 ^ q) ^ 4 := by rw [← pow_mul]; congr 1; ring
  have hnr : (A : ℚ) * (D : ℚ) ^ 8 ≤ ((2 ^ q : ℕ) : ℚ) ^ 4 := by exact_mod_cast hn
  have hl : 1 ≤ (p.eta * ((528 * x.n ^ (B1 + 4) : ℕ) : ℚ)) ^ 8 :=
    one_le_pow₀ (hs.eta_scale_lower B1 hb)
  rw [mul_pow] at hl
  apply (hs.Qexp_le_iff q).mpr
  rw [← Nat.cast_pow, ← Nat.cast_mul]
  change (A : ℚ) ≤ ((2 ^ q : ℕ) : ℚ) ^ 4 * p.eta ^ 8
  calc
    (A : ℚ) ≤ (A : ℚ) * ((D : ℚ) ^ 8 * p.eta ^ 8) := by
      have h := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (A : ℚ))
      simpa only [D, mul_one, mul_comm, mul_left_comm, mul_assoc] using h
    _ = ((A : ℚ) * (D : ℚ) ^ 8) * p.eta ^ 8 := by ring
    _ ≤ ((2 ^ q : ℕ) : ℚ) ^ 4 * p.eta ^ 8 :=
      mul_le_mul_of_nonneg_right hnr (by positivity)

/-- `lem:asymptotics` and `prop:time`, paper/paper.tex: the integer form consumed by the running-time ledger. -/
theorem Qexp_four_upper (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    4 * p.Qexp ≤ 3 * p.k + 4 * (2 * B1 + 100) * p.lambda := by
  have hq := hs.Qexp_upper B1 hb
  have hf := Nat.div_mul_le_self (3 * p.k) 4
  nlinarith

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: both actual
Fourier periods are bounded by `33 n⁴`. -/
theorem omega_upper (hs : ParameterRules x p) :
    p.omega1 ≤ 33 * x.n ^ 4 ∧ p.omega2 ≤ 33 * x.n ^ 4 :=
  CoreRules.omega_upper (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the actual
Fourier mass envelope is bounded by `33 n⁴`. -/
theorem MF_upper (hs : ParameterRules x p) : p.MF ≤ 33 * x.n ^ 4 :=
  CoreRules.MF_upper (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the sampler
tolerance is bounded below by an explicit polynomial scale independent of
the denominator used to encode the precision. -/
theorem eta_scale_lower (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    1 ≤ p.eta * ((528 * x.n ^ (B1 + 4) : ℕ) : ℚ) :=
  CoreRules.eta_scale_lower (hs : CoreRules x p) B1 hb

/-- `lem:asymptotics`, paper/paper.tex: the sixth power
of the actual matrix side is bounded by the exact inner-dimension exponent. -/
theorem N_sixth (hs : ParameterRules x p) : p.N ^ 6 ≤ 2 ^ (3 * p.k) :=
  CoreRules.N_sixth (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the literal
fourth-power sample numerator, multiplied by the eighth power of the tolerance
scale, has the required binary upper bound. -/
theorem sample_scaled_binary (hs : ParameterRules x p) (B1 : ℕ) :
    ((1024 * p.N * p.m) ^ 4 * (4 * p.N ^ 2 * (2 * (p.omega1 * p.omega2)))) *
      (528 * x.n ^ (B1 + 4)) ^ 8 ≤
        2 ^ (143 + 3 * p.k + (8 * B1 + 40) * p.lambda) :=
  CoreRules.sample_scaled_binary (hs : CoreRules x p) B1

/-- `lem:asymptotics`, paper/paper.tex: the actual least
dyadic sampler size has coefficient three quarters in the inner dimension. -/
theorem Qexp_upper (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    p.Qexp ≤ (3 * p.k) / 4 + (2 * B1 + 100) * p.lambda :=
  CoreRules.Qexp_upper (hs : CoreRules x p) B1 hb

/-- `lem:asymptotics` and `prop:time`, paper/paper.tex: the integer form consumed by the running-time ledger. -/
theorem Qexp_four_upper (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    4 * p.Qexp ≤ 3 * p.k + 4 * (2 * B1 + 100) * p.lambda :=
  CoreRules.Qexp_four_upper (hs : CoreRules x p) B1 hb

end NearQuarticWires.Cells.ParameterRules

