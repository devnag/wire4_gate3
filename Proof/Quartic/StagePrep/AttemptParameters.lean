import Proof.Quartic.StagePrep.SelectionTail

/-!
# A total finite description of the parameter attempt

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open Cells.ParameterArithmetic
open NearCubicGates.Close.Counter

/-- A total finite record of the parameter attempt in
`sec:params`, paper/paper.tex. Missing lift or
stopping results are stored as zero only for describing later
inactive fields; the executed guards still reject those cases. -/
def attemptPublicParameters (x : Cells.ParameterInput) (p : Cells.Parameters) :
    Cells.Parameters :=
  let Dmax := Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n
  let P := Nat.findGreatest (PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax Dmax) x.n
  let e := (liftExponent p.BN P).getD 0
  let primes := dyadicPrimes P
  let Dprime := NearCubicGates.ScalarWindow.window primes
  let L2 := pairSide Dprime
  let Lw := windowInUse x.pair L2 Dprime
  let hE := P / 4
  let h := hE / (2 * p.m)
  let ell0 : ℚ := (32 * p.m * p.U : ℕ)
  let ratio := firstRatio ell0 h p.T
  let i := (stopIndex ratio x.n).getD 0
  let factors := chainFactors ratio i
  let A := factors.prod
  { p with
    Dmax := Dmax
    P := P
    e := e
    hE := hE
    h := h
    Lw := Lw
    primes := primes
    Dprime := Dprime
    L2 := L2
    M1 := firstDen ell0 h p.T
    J := i + 1
    A := A
    Lambda := (Lw - 1) * A / 2 + 1
    ell0 := ell0
    factors := factors }

/-- The literal guards of `sec:params`, paper/paper.tex, including missing stopping results, evaluated
on the total finite attempt record. -/
def attemptPass (x : Cells.ParameterInput) (p : Cells.Parameters) : Prop :=
  DegreePass x.n p.m p.k p.Uocc 0 ∧
    PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax p.Dmax p.P ∧
    4*p.m*p.Xmax+2*p.m*p.k≤p.Dmax ∧ p.primes.Nonempty ∧ 64*p.T≤p.h ∧
    (stopIndex (firstRatio p.ell0 p.h p.T) x.n).isSome=true ∧ p.J≤p.Jmax

instance (x : Cells.ParameterInput) (p : Cells.Parameters) : Decidable (attemptPass x p) := by
  unfold attemptPass
  infer_instance

/-- All early public identities of `sec:params`,
paper/paper.tex, remain exact in the total
attempt record, independently of every later guard outcome. -/
theorem attemptPublicParameters_core (x : Cells.ParameterInput) (p : Cells.Parameters)
    (hs : Cells.CoreRules x p) : Cells.CoreRules x (attemptPublicParameters x p) := by
  exact {
    input_valid := hs.input_valid
    lambda_eq := hs.lambda_eq
    mu_eq := hs.mu_eq
    m_eq := hs.m_eq
    r_eq := hs.r_eq
    r_bound := hs.r_bound
    s_eq := hs.s_eq
    b_eq := hs.b_eq
    k_eq := hs.k_eq
    N_eq := hs.N_eq
    Jmax_eq := hs.Jmax_eq
    T_eq := hs.T_eq
    tau_eq := hs.tau_eq
    U_eq := hs.U_eq
    pi0_eq := hs.pi0_eq
    Xmax_eq := hs.Xmax_eq
    dstar_eq := hs.dstar_eq
    omega1_eq := hs.omega1_eq
    omega2_eq := hs.omega2_eq
    MF_eq := hs.MF_eq
    eta_eq := hs.eta_eq
    Qexp_eq := hs.Qexp_eq
    Q_eq := hs.Q_eq
    ellf_eq := hs.ellf_eq
    S_eq := hs.S_eq
    NatAtoms_eq := hs.NatAtoms_eq
    childCap_eq := hs.childCap_eq
    Uocc_eq := hs.Uocc_eq
    BN_eq := hs.BN_eq }

/-- The exact finite selector of `sec:params`,
paper/paper.tex, accepts the total attempt
record precisely when every literal public guard succeeds.
Failed optional results never become accepted zero defaults. -/
theorem selectPublicParameters_eq_attempt (x : Cells.ParameterInput) (p : Cells.Parameters) :
    selectPublicParameters x p =
      if attemptPass x (attemptPublicParameters x p) then
        some (attemptPublicParameters x p) else none := by
  classical
  unfold selectPublicParameters attemptPass attemptPublicParameters
  dsimp only
  split
  swap
  · simp_all
  rename_i hdegree
  simp only [hdegree,true_and]
  split
  swap
  · simp_all
  rename_i hprime
  simp only [hprime,true_and]
  split
  · rename_i hnone
    have hfalse : False := by
      have hcheck := hprime.2.2
      rw [hnone] at hcheck
      exact hcheck
    exact hfalse.elim
  rename_i e he
  simp only [he,Option.getD_some]
  split
  swap
  · simp_all
  rename_i hmoment
  simp only [hmoment,true_and]
  split
  swap
  · simp_all
  rename_i hprimes
  simp only [hprimes,true_and]
  split
  swap
  · simp_all
  rename_i hheight
  simp only [hheight,true_and]
  split
  · simp_all
  rename_i i hi
  simp only [hi,Option.getD_some,Option.isSome_some,true_and]

end NearQuarticWires.StagePrep
