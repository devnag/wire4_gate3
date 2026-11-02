import Proof.Quartic.Cells.ParametersPublic
import Proof.Quartic.Cells.ParametersEncodingEnvelope

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

namespace ParameterArithmetic

/-- `prop:time`, paper/paper.tex: a polynomial
value bound yields a linear binary-height bound at each fixed degree. -/
theorem polynomial_value_binary_bound (a n degree : ℕ) :
    a * n ^ degree ≤ 2 ^ (a + degree * n) := by
  have ha : a ≤ 2 ^ a := Nat.lt_two_pow_self.le
  have hn : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
  calc
    a * n ^ degree ≤ 2 ^ a * (2 ^ n) ^ degree :=
      Nat.mul_le_mul ha (Nat.pow_le_pow_left hn _)
    _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm n degree]

/-- `sec:params` and `prop:time`, paper/paper.tex: the preparation value envelope itself has linear
binary height, rather than its polynomial value as its height. -/
theorem preparation_envelope_binary_bound (B1 n : ℕ) :
    preparationEnvelope B1 n ≤
      2 ^ (preparationCoefficient B1 + (B1 + 12) * (n + 1)) :=
  polynomial_value_binary_bound _ _ _

end ParameterArithmetic

/-- `sec:params` and `prop:time`, paper/paper.tex: polynomial value bounds for the early computations,
before the degree, prime and rate-chain acceptance tests. -/
structure EarlyPreparationBounds (B1 : ℕ) (x : ParameterInput) (p : Parameters) : Prop where
  k : p.k ≤ preparationEnvelope B1 x.n
  T : p.T ≤ preparationEnvelope B1 x.n
  tau : p.tau ≤ preparationEnvelope B1 x.n
  U : p.U ≤ preparationEnvelope B1 x.n
  Xmax : p.Xmax ≤ preparationEnvelope B1 x.n
  dstar : p.dstar ≤ preparationEnvelope B1 x.n
  omega1 : p.omega1 ≤ preparationEnvelope B1 x.n
  omega2 : p.omega2 ≤ preparationEnvelope B1 x.n
  MF : p.MF ≤ preparationEnvelope B1 x.n
  Qexp : p.Qexp ≤ preparationEnvelope B1 x.n
  ellf : p.ellf ≤ preparationEnvelope B1 x.n
  S : p.S ≤ preparationEnvelope B1 x.n
  BN : p.BN ≤ preparationEnvelope B1 x.n
  pi0_denominator : 4 * p.U ≤ preparationEnvelope B1 x.n
  ell0_numerator : 128 * p.U ≤ preparationEnvelope B1 x.n
  eta_divisor : 16 * p.MF ≤ preparationEnvelope B1 x.n
  Xmax_radicand : 9 * p.tau ^ 2 * x.n * p.r ≤
    9 * preparationEnvelope B1 x.n ^ 4
  theta : 2 * (p.omega1 * p.omega2) ≤ 2 * preparationEnvelope B1 x.n ^ 2

namespace CoreRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the actual radicand
searched for the integer population root has polynomial value before
any later parameter-selection test. -/
theorem Xmax_radicand_preparation_bound (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    9 * p.tau ^ 2 * x.n * p.r ≤ 144 * (B1 + 20) ^ 2 * x.n ^ 6 := by
  have hr : p.r ≤ 16 * x.n := by
    rw [hs.r_eq]
    exact Nat.mul_le_mul_left _ (hs.mu_le_lambda.trans hs.lambda_le_n)
  calc
    9 * p.tau ^ 2 * x.n * p.r ≤
        9 * ((B1 + 20) * x.n ^ 2) ^ 2 * x.n * (16 * x.n) := by
      gcongr
      exact hs.tau_preparation_bound B1 hb
    _ = _ := by ring

/-- `sec:params`, paper/paper.tex: the Fourier
parameter supplied to the sample exponent has polynomial value
before any later acceptance test. -/
theorem theta_preparation_bound (hs : CoreRules x p) :
    2 * (p.omega1 * p.omega2) ≤ 2178 * x.n ^ 8 := by
  calc
    2 * (p.omega1 * p.omega2) ≤ 2 * ((33 * x.n ^ 4) * (33 * x.n ^ 4)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hs.omega_upper.1 hs.omega_upper.2)
    _ = _ := by ring

/-- `sec:params` and `prop:time`, paper/paper.tex: all early loop bounds and scalar operands are polynomially
bounded under admitted precision, including computations that later reject. -/
theorem early_preparation_bounds (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : EarlyPreparationBounds B1 x p := by
  let V := preparationEnvelope B1 x.n
  have base (a degree : ℕ) (ha : a ∈ preparationCoefficients B1) (hd : degree ≤ B1 + 12) :
      a * x.n ^ degree ≤ V := preparation_envelope_base B1 x.n a degree ha hd
  have succ (a degree : ℕ) (ha : a ∈ preparationCoefficients B1) (hd : degree ≤ B1 + 12) :
      a * (x.n + 1) ^ degree ≤ V := preparation_envelope_succ B1 x.n a degree ha hd
  have hN : x.n ≤ V := (Nat.le_succ _).trans (preparation_envelope_arity B1 x.n)
  have hr : p.r ≤ V := (by have := hs.r_bound; omega : p.r ≤ x.n).trans hN
  have htau : p.tau ≤ V := (hs.tau_preparation_bound B1 hb).trans
    (base (B1 + 20) 2 (by simp [preparationCoefficients]) (by omega))
  have hw1 : p.omega1 ≤ V := hs.omega_upper.1.trans
    (base 33 4 (by simp [preparationCoefficients]) (by omega))
  have hw2 : p.omega2 ≤ V := hs.omega_upper.2.trans
    (base 33 4 (by simp [preparationCoefficients]) (by omega))
  have hseeds := hs.seed_preparation_bound B1 hb
  refine {
    k := hs.k_preparation_bound.trans (base 16 2 (by simp [preparationCoefficients]) (by omega))
    T := (hs.T_preparation_bound B1 hb).trans (base (B1 + 80) 2 (by simp [preparationCoefficients]) (by omega))
    tau := htau
    U := (hs.U_preparation_bound B1 hb).trans (base (B1 + 20000) (B1 + 4) (by simp [preparationCoefficients]) (by omega))
    Xmax := (hs.Xmax_preparation_bound B1 hb).trans (base (48 * (B1 + 20)) 4 (by simp [preparationCoefficients]) (by omega))
    dstar := (hs.dstar_preparation_bound B1 hb).trans
      (base (96 * (B1 + 20) * (B1 + 20000)) (B1 + 8) (by simp [preparationCoefficients]) (by omega))
    omega1 := hw1
    omega2 := hw2
    MF := hs.MF_upper.trans (base 33 4 (by simp [preparationCoefficients]) (by omega))
    Qexp := (hs.Qexp_preparation_bound B1 hb).trans (base (2 * B1 + 112) 2 (by simp [preparationCoefficients]) (by omega))
    ellf := hseeds.1.trans (succ (2 * B1 + 130) 2 (by simp [preparationCoefficients]) (by omega))
    S := hseeds.2.trans (succ (8 * (2 * B1 + 130)) 2 (by simp [preparationCoefficients]) (by omega))
    BN := (hs.BN_preparation_bound B1 hb).trans (base (32 * B1 + 2200) 2 (by simp [preparationCoefficients]) (by omega))
    pi0_denominator := ?_
    ell0_numerator := ?_
    eta_divisor := ?_
    Xmax_radicand := ?_
    theta := ?_ }
  · calc
      4 * p.U ≤ 4 * ((B1 + 20000) * x.n ^ (B1 + 4)) := Nat.mul_le_mul_left _ (hs.U_preparation_bound B1 hb)
      _ = (4 * (B1 + 20000)) * x.n ^ (B1 + 4) := by ring
      _ ≤ V := base _ _ (by simp [preparationCoefficients]) (by omega)
  · calc
      128 * p.U ≤ 128 * ((B1 + 20000) * x.n ^ (B1 + 4)) := Nat.mul_le_mul_left _ (hs.U_preparation_bound B1 hb)
      _ = (128 * (B1 + 20000)) * x.n ^ (B1 + 4) := by ring
      _ ≤ V := base _ _ (by simp [preparationCoefficients]) (by omega)
  · calc
      16 * p.MF ≤ 16 * (33 * x.n ^ 4) := Nat.mul_le_mul_left _ hs.MF_upper
      _ = 528 * x.n ^ 4 := by ring
      _ ≤ V := base 528 4 (by simp [preparationCoefficients]) (by omega)
  · calc
      9 * p.tau ^ 2 * x.n * p.r ≤ 9 * V ^ 2 * V * V := by gcongr
      _ = _ := by ring
  · calc
      2 * (p.omega1 * p.omega2) ≤ 2 * (V * V) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hw1 hw2)
      _ = _ := by ring

/-- `sec:params` and `prop:time`, paper/paper.tex: the two exponentially valued public fields have
polynomial stored length before any later acceptance test. -/
theorem early_exponential_field_words (hs : CoreRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    (NearCubicWires.RepairRepresentation.natWord p.N).length ≤ 16 * x.n ^ 2 + 3 ∧
    (NearCubicWires.RepairRepresentation.natWord p.Q).length ≤
      (4 * B1 + 224) * x.n ^ 2 + 3 := by
  have hk := hs.k_preparation_bound
  have hN : (NearCubicWires.RepairRepresentation.natWord p.N).length ≤ p.k + 3 := by
    rw [hs.N_eq]
    have h := natWord_length_of_power_bound (2 ^ (p.k / 2)) (p.k / 2) le_rfl
    omega
  have hQ : (NearCubicWires.RepairRepresentation.natWord p.Q).length ≤ 2 * p.Qexp + 3 := by
    rw [hs.Q_eq]
    exact natWord_length_of_power_bound _ _ le_rfl
  have hq := hs.Qexp_preparation_bound B1 hb
  constructor <;> nlinarith only [hk, hN, hQ, hq]

/-- `sec:params` and `prop:time`, paper/paper.tex: the canonical numerator and denominator of the two
early rational scales have polynomial bit length, including on calls
that reject at a later degree, prime or rate-chain test. -/
theorem early_rational_preparation_bounds (hs : CoreRules x p) (B1 L : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1)
    (hnum : x.beta.num.natAbs ≤ 2 ^ L) (hden : x.beta.den ≤ 2 ^ L) :
    let B := preparationEnvelope B1 x.n + L
    (p.pi0.num.natAbs ≤ 2 ^ B ∧ p.pi0.den ≤ 2 ^ B) ∧
      (p.eta.num.natAbs ≤ 2 ^ B ∧ p.eta.den ≤ 2 ^ B) := by
  have hscalar := hs.early_preparation_bounds B1 hb
  let V := preparationEnvelope B1 x.n
  have hv : V ≤ 2 ^ V := Nat.lt_two_pow_self.le
  have hpow : 2 ^ V ≤ 2 ^ (V + L) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  have hpowL : 2 ^ L ≤ 2 ^ (V + L) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  have hkpos : 0 < p.k := by
    rw [hs.k_eq]
    exact Nat.mul_pos (by have := hs.r_even_large.2; omega)
      (by rw [← hs.star_s]; exact hs.starParams.one_le_s)
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
  have hηb := div_natCast_size_bounds x.beta (16 * p.MF) (by have := hs.MF_pos; positivity)
  have hηN : p.eta.num.natAbs ≤ 2 ^ (V + L) := by
    rw [heta]
    exact hηb.1.trans (hnum.trans hpowL)
  have hηD : p.eta.den ≤ 2 ^ (V + L) := by
    rw [heta]
    calc
      (x.beta / ((16 * p.MF : ℕ) : ℚ)).den ≤ x.beta.den * (16 * p.MF) := hηb.2
      _ ≤ 2 ^ L * 2 ^ V := Nat.mul_le_mul hden (hscalar.eta_divisor.trans hv)
      _ = 2 ^ (V + L) := by rw [← pow_add, Nat.add_comm]
  exact ⟨⟨hpiN.trans (hv.trans hpow), hpiD.trans (hv.trans hpow)⟩, ⟨hηN, hηD⟩⟩

end CoreRules

/-- `sec:params` and `prop:time`, paper/paper.tex: the literal public prefix has polynomial loop bounds
using only its admission, initial geometry and precision hypotheses. -/
theorem publicScales_early_preparation_bounds (B1 : ℕ) (x : ParameterInput)
    (hv : ValidInput x) (hr : 4 * (16 * NearCubicGates.Target.mu x.n) ≤ x.n)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) :
    EarlyPreparationBounds B1 x (publicScales x) :=
  (publicScales_core x hv hr).early_preparation_bounds B1 hb

end NearQuarticWires.Cells
