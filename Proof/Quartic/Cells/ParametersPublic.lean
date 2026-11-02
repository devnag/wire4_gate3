import Proof.Quartic.Cells.AsymptoticsSeed
import Proof.Gates.Closure.Asymptotics

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params`, paper/paper.tex: the initial public
scales, extended by zero in the later selection coordinates for analysing the
degree, prime and rate-chain tests. -/
def publicScales (x : ParameterInput) : Parameters :=
  let lam := NearCubicGates.Target.lambda x.n
  let mu := NearCubicGates.Target.mu x.n
  let m := 4
  let r := 16 * mu
  let s := Nat.log 2 (x.n / r + 1)
  let b := 2 ^ s - 1
  let k := r * s
  let N := 2 ^ (k / 2)
  let Jmax := mu + 1
  let T := concentrationT m k Jmax x.beta
  let tau := k + ceilLog 2 (16 / x.beta)
  let U := max tau (ceilSqrtRat ((96 ^ 2 * (r : ℚ) ^ 3 * (x.W : ℚ) ^ 2) /
    (x.beta ^ 2 * (x.n : ℚ) ^ 3)))
  let pi0 := (tau : ℚ) / (4 * U)
  let Xmax := ceilSqrt (9 * tau ^ 2 * x.n * r)
  let dstar := 2 * Xmax * U / (3 * r * tau)
  let omega1 := 4 * m * x.G1 + 1
  let omega2 := 4 * m * x.G2 + 1
  let MF := ceilSqrt (omega1 * omega2)
  let eta := x.beta / (16 * MF)
  let Qexp := sampleExponent N m (2 * (omega1 * omega2)) eta
  let Q := 2 ^ Qexp
  let ellf := max k (Qexp + 1)
  let S := 2 * m * ellf
  let NatAtoms := (4 * m + 1) * (2 * x.n ^ 4)
  let cap := childCap x.n (NearCubicGates.Close.Counter.B0 x.n)
  let Uocc := 1 + NatAtoms * cap
  let BN := S + m * k + 2 * m * Nat.clog 2 (N ^ 2 * Q) + 1
  { lambda := lam, mu := mu, m := m, r := r, s := s, b := b, k := k, N := N,
    Jmax := Jmax, T := T, tau := tau, U := U, Xmax := Xmax, dstar := dstar,
    omega1 := omega1, omega2 := omega2, MF := MF, Q := Q, ellf := ellf, S := S,
    NatAtoms := NatAtoms, childCap := cap, Uocc := Uocc, Dmax := 0, BN := BN,
    P := 0, e := 0, hE := 0, h := 0, Lw := 0, pi0 := pi0, eta := eta,
    Qexp := Qexp, primes := ∅, Dprime := 0, L2 := 0, M1 := 0, J := 0,
    A := 0, Lambda := 0, ell0 := 0, factors := [] }

/-- `sec:params`, paper/paper.tex: the computed early
scales satisfy their exact identities before any degree, prime or chain test. -/
theorem publicScales_core (x : ParameterInput) (hv : ValidInput x)
    (hr : 4 * (16 * NearCubicGates.Target.mu x.n) ≤ x.n) : CoreRules x (publicScales x) := by
  exact {
    input_valid := hv
    lambda_eq := rfl
    mu_eq := rfl
    m_eq := rfl
    r_eq := rfl
    r_bound := hr
    s_eq := rfl
    b_eq := rfl
    k_eq := rfl
    N_eq := rfl
    Jmax_eq := rfl
    T_eq := rfl
    tau_eq := rfl
    U_eq := rfl
    pi0_eq := rfl
    Xmax_eq := rfl
    dstar_eq := rfl
    omega1_eq := rfl
    omega2_eq := rfl
    MF_eq := rfl
    eta_eq := rfl
    Qexp_eq := rfl
    Q_eq := rfl
    ellf_eq := rfl
    S_eq := rfl
    NatAtoms_eq := rfl
    childCap_eq := rfl
    Uocc_eq := rfl
    BN_eq := rfl }

/-- `lem:asymptotics`, paper/paper.tex: the initial
block-count requirement holds at all sufficiently large input lengths. -/
theorem eventual_initial_geometry : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ n : ℕ, onset ≤ n → 4 * (16 * NearCubicGates.Target.mu n) ≤ n := by
  obtain ⟨onset, hon, hb⟩ := NearCubicGates.Close.Closure.lambda_poly_lt 64 1
  refine ⟨onset, hon, fun n hn => ?_⟩
  have h := hb n hn
  simp only [pow_one] at h
  have hm : NearCubicGates.Target.mu n ≤ NearCubicGates.Target.lambda n :=
    NearCubicGates.Close.Counter.clog_le_self _
  omega

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: every normalized nonconstant call eventually supplies the
complete early-scale identities, independently of all later acceptance tests. -/
theorem eventual_publicScales_core : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x → CoreRules x (publicScales x) := by
  obtain ⟨onset, hon, hr⟩ := eventual_initial_geometry
  exact ⟨onset, hon, fun x hn hv => publicScales_core x hv (hr x.n hn)⟩

/-- `lem:asymptotics` and `prop:complete`, paper/paper.tex: unconditional uniform bounds and precision side conditions for the
computed public scales under admitted polynomial precision. -/
theorem eventual_publicScales_bounds (B1 : ℕ) : ∃ onset : ℕ, 4 ≤ onset ∧
    ∀ x : ParameterInput, onset ≤ x.n → ValidInput x → 1 ≤ x.beta * (x.n : ℚ) ^ B1 →
      let p := publicScales x
      (8 * p.mu * p.lambda ≤ p.k ∧ p.k ≤ 16 * p.mu * p.lambda) ∧
      p.T ≤ (B1 + 80) * p.mu * p.lambda ∧ p.tau ≤ (B1 + 20) * p.mu * p.lambda ∧
      4 * p.Qexp ≤ 3 * p.k + 4 * (2 * B1 + 100) * p.lambda ∧
      p.ellf = p.k ∧ p.S = 8 * p.k ∧ ceilLog 2 (16 / x.beta) ≤ p.k ∧
      2 * p.k + 2 * ceilLog 2 (64 / x.beta) ≤ p.Xmax := by
  obtain ⟨oc, hoc, hc⟩ := eventual_publicScales_core
  obtain ⟨ok, hok, hk⟩ := CoreRules.eventual_k_bounds
  obtain ⟨os, hos, hseed⟩ := CoreRules.eventual_seed_length B1
  obtain ⟨op, hop, hprec⟩ := CoreRules.eventual_k_precision B1
  refine ⟨max (max oc ok) (max os op), by omega, ?_⟩
  intro x hn hv hb
  have hs := hc x (by omega) hv
  have hslen := hseed x (publicScales x) (by omega) hs hb
  exact ⟨hk x (publicScales x) (by omega) hs, hs.T_upper B1 hb, hs.tau_upper B1 hb,
    hs.Qexp_four_upper B1 hb, hslen.1, hslen.2,
    hprec x (publicScales x) (by omega) hs hb, hs.Xmax_precision⟩

end NearQuarticWires.Cells
