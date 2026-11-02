import Proof.Quartic.Cells.ParametersEncodingEnvelope

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- The scalar fields of the literal parameter record in `sec:params`,
paper/paper.tex, all fit one polynomial value envelope.
The two power-of-two fields are controlled through their stored exponents. -/
structure ScalarPreparationBounds (B1 : ℕ) (x : ParameterInput) (p : Parameters) : Prop where
  lambda : p.lambda ≤ preparationEnvelope B1 x.n
  mu : p.mu ≤ preparationEnvelope B1 x.n
  m : p.m ≤ preparationEnvelope B1 x.n
  r : p.r ≤ preparationEnvelope B1 x.n
  s : p.s ≤ preparationEnvelope B1 x.n
  b : p.b ≤ preparationEnvelope B1 x.n
  k : p.k ≤ preparationEnvelope B1 x.n
  Jmax : p.Jmax ≤ preparationEnvelope B1 x.n
  T : p.T ≤ preparationEnvelope B1 x.n
  tau : p.tau ≤ preparationEnvelope B1 x.n
  U : p.U ≤ preparationEnvelope B1 x.n
  Xmax : p.Xmax ≤ preparationEnvelope B1 x.n
  dstar : p.dstar ≤ preparationEnvelope B1 x.n
  omega1 : p.omega1 ≤ preparationEnvelope B1 x.n
  omega2 : p.omega2 ≤ preparationEnvelope B1 x.n
  MF : p.MF ≤ preparationEnvelope B1 x.n
  ellf : p.ellf ≤ preparationEnvelope B1 x.n
  S : p.S ≤ preparationEnvelope B1 x.n
  NatAtoms : p.NatAtoms ≤ preparationEnvelope B1 x.n
  childCap : p.childCap ≤ preparationEnvelope B1 x.n
  Uocc : p.Uocc ≤ preparationEnvelope B1 x.n
  Dmax : p.Dmax ≤ preparationEnvelope B1 x.n
  BN : p.BN ≤ preparationEnvelope B1 x.n
  P : p.P ≤ preparationEnvelope B1 x.n
  e : p.e ≤ preparationEnvelope B1 x.n
  hE : p.hE ≤ preparationEnvelope B1 x.n
  h : p.h ≤ preparationEnvelope B1 x.n
  Lw : p.Lw ≤ preparationEnvelope B1 x.n
  Qexp : p.Qexp ≤ preparationEnvelope B1 x.n
  Dprime : p.Dprime ≤ preparationEnvelope B1 x.n
  L2 : p.L2 ≤ preparationEnvelope B1 x.n
  M1 : p.M1 ≤ preparationEnvelope B1 x.n
  J : p.J ≤ preparationEnvelope B1 x.n
  A : p.A ≤ preparationEnvelope B1 x.n
  Lambda : p.Lambda ≤ preparationEnvelope B1 x.n
  pi0_denominator : 4 * p.U ≤ preparationEnvelope B1 x.n
  ell0_numerator : 128 * p.U ≤ preparationEnvelope B1 x.n
  eta_divisor : 16 * p.MF ≤ preparationEnvelope B1 x.n

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params` and `prop:time`, paper/paper.tex: every actual selected scalar field, and the natural
scales in the three rational fields, fit one common polynomial envelope. -/
theorem scalar_preparation_bounds (hs : ParameterRules x p) (B1 : ℕ)
    (hb : 1 ≤ x.beta * (x.n : ℚ) ^ B1) : ScalarPreparationBounds B1 x p := by
  have hc : CoreRules x p := hs
  let V := preparationEnvelope B1 x.n
  have base (a degree : ℕ) (ha : a ∈ preparationCoefficients B1) (hd : degree ≤ B1 + 12) :
      a * x.n ^ degree ≤ V := preparation_envelope_base B1 x.n a degree ha hd
  have succ (a degree : ℕ) (ha : a ∈ preparationCoefficients B1) (hd : degree ≤ B1 + 12) :
      a * (x.n + 1) ^ degree ≤ V := preparation_envelope_succ B1 x.n a degree ha hd
  have hN1 : x.n + 1 ≤ V := preparation_envelope_arity B1 x.n
  have hN : x.n ≤ V := (Nat.le_succ _).trans hN1
  have hN2 : x.n ^ 2 ≤ V := by
    simpa only [one_mul] using base 1 2 (by simp [preparationCoefficients]) (by omega)
  have hL := hc.lambda_le_n
  have hM := hc.mu_le_lambda.trans hL
  have hP := hs.prime_candidate.2.1
  have hD : p.Dprime ≤ x.n ^ 2 := hs.scalar_window_upper.trans (Nat.pow_le_pow_left hP _)
  have hLw : p.Lw ≤ p.Dprime := by
    rw [hs.Lw_eq]
    unfold NearCubicGates.Close.Counter.windowInUse
    split_ifs
    · exact hs.window_bounds.2.1
    · exact le_rfl
  have hJmax : p.Jmax ≤ x.n + 1 := by rw [hs.Jmax_eq]; omega
  have he : p.e ≤ (32 * B1 + 2201) * (x.n + 1) ^ 2 := by
    have he0 := hs.lift_spec.2.1
    have hBN := hc.BN_preparation_bound B1 hb
    nlinarith only [he0, hBN, Nat.zero_le B1, Nat.zero_le x.n]
  have hchild : p.childCap ≤ 8 * x.n ^ 3 := by
    calc
      p.childCap ≤ 8 * x.n ^ 2 * p.lambda := hc.childCap_le
      _ ≤ 8 * x.n ^ 2 * x.n := Nat.mul_le_mul_left _ hL
      _ = _ := by ring
  have hocc : p.Uocc ≤ 273 * x.n ^ 7 := by
    calc
      p.Uocc ≤ 273 * x.n ^ 6 * p.lambda := hc.Uocc_polynomial
      _ ≤ 273 * x.n ^ 6 * x.n := Nat.mul_le_mul_left _ hL
      _ = _ := by ring
  have hseeds := hc.seed_preparation_bound B1 hb
  have hrates := hs.rate_values_preparation_bound B1 hb
  refine {
    lambda := hL.trans hN
    mu := hM.trans hN
    m := by rw [hs.m_eq]; exact hs.input_valid.1.trans hN
    r := ?_
    s := (hc.s_le_lambda.trans hL).trans hN
    b := hc.b_preparation_bound.trans hN
    k := hc.k_preparation_bound.trans (base 16 2 (by simp [preparationCoefficients]) (by omega))
    Jmax := hJmax.trans hN1
    T := (hc.T_preparation_bound B1 hb).trans (base (B1 + 80) 2 (by simp [preparationCoefficients]) (by omega))
    tau := (hc.tau_preparation_bound B1 hb).trans (base (B1 + 20) 2 (by simp [preparationCoefficients]) (by omega))
    U := (hc.U_preparation_bound B1 hb).trans (base (B1 + 20000) (B1 + 4) (by simp [preparationCoefficients]) (by omega))
    Xmax := (hc.Xmax_preparation_bound B1 hb).trans (base (48 * (B1 + 20)) 4 (by simp [preparationCoefficients]) (by omega))
    dstar := (hc.dstar_preparation_bound B1 hb).trans
      (base (96 * (B1 + 20) * (B1 + 20000)) (B1 + 8) (by simp [preparationCoefficients]) (by omega))
    omega1 := hc.omega_upper.1.trans (base 33 4 (by simp [preparationCoefficients]) (by omega))
    omega2 := hc.omega_upper.2.trans (base 33 4 (by simp [preparationCoefficients]) (by omega))
    MF := hc.MF_upper.trans (base 33 4 (by simp [preparationCoefficients]) (by omega))
    ellf := hseeds.1.trans (succ (2 * B1 + 130) 2 (by simp [preparationCoefficients]) (by omega))
    S := hseeds.2.trans (succ (8 * (2 * B1 + 130)) 2 (by simp [preparationCoefficients]) (by omega))
    NatAtoms := ?_
    childCap := hchild.trans (base 8 3 (by simp [preparationCoefficients]) (by omega))
    Uocc := hocc.trans (base 273 7 (by simp [preparationCoefficients]) (by omega))
    Dmax := ?_
    BN := (hc.BN_preparation_bound B1 hb).trans (base (32 * B1 + 2200) 2 (by simp [preparationCoefficients]) (by omega))
    P := hP.trans hN
    e := he.trans (succ (32 * B1 + 2201) 2 (by simp [preparationCoefficients]) (by omega))
    hE := ?_
    h := ?_
    Lw := (hLw.trans hD).trans hN2
    Qexp := (hc.Qexp_preparation_bound B1 hb).trans (base (2 * B1 + 112) 2 (by simp [preparationCoefficients]) (by omega))
    Dprime := hD.trans hN2
    L2 := (hs.window_bounds.2.1.trans hD).trans hN2
    M1 := hrates.1.trans (base (512 * (B1 + 20000) + 4) (B1 + 4) (by simp [preparationCoefficients]) (by omega))
    J := (hs.J_bound.trans hJmax).trans hN1
    A := hrates.2.1.trans (base (512 * (B1 + 20000) + 4) (B1 + 4) (by simp [preparationCoefficients]) (by omega))
    Lambda := hrates.2.2.trans (succ (512 * (B1 + 20000) + 5) (B1 + 6) (by simp [preparationCoefficients]) (by omega))
    pi0_denominator := ?_
    ell0_numerator := ?_
    eta_divisor := ?_ }
  · rw [hs.r_eq]
    exact (Nat.mul_le_mul_left 16 hM).trans
      (by simpa only [pow_one] using base 16 1 (by simp [preparationCoefficients]) (by omega))
  · calc
      p.NatAtoms = 34 * x.n ^ 4 := by rw [hs.NatAtoms_eq, hs.m_eq]; ring
      _ ≤ V := base 34 4 (by simp [preparationCoefficients]) (by omega)
  · rw [hs.Dmax_eq]
    exact (Nat.findGreatest_le _).trans hN
  · rw [hs.hE_eq]
    exact ((Nat.div_le_self _ _).trans hP).trans hN
  · rw [hs.h_eq, hs.hE_eq]
    exact ((Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hP)).trans hN
  · calc
      4 * p.U ≤ 4 * ((B1 + 20000) * x.n ^ (B1 + 4)) := Nat.mul_le_mul_left _ (hc.U_preparation_bound B1 hb)
      _ = (4 * (B1 + 20000)) * x.n ^ (B1 + 4) := by ring
      _ ≤ V := base _ _ (by simp [preparationCoefficients]) (by omega)
  · calc
      128 * p.U ≤ 128 * ((B1 + 20000) * x.n ^ (B1 + 4)) := Nat.mul_le_mul_left _ (hc.U_preparation_bound B1 hb)
      _ = (128 * (B1 + 20000)) * x.n ^ (B1 + 4) := by ring
      _ ≤ V := base _ _ (by simp [preparationCoefficients]) (by omega)
  · calc
      16 * p.MF ≤ 16 * (33 * x.n ^ 4) := Nat.mul_le_mul_left _ hc.MF_upper
      _ = 528 * x.n ^ 4 := by ring
      _ ≤ V := base 528 4 (by simp [preparationCoefficients]) (by omega)

end ParameterRules

end NearQuarticWires.Cells
