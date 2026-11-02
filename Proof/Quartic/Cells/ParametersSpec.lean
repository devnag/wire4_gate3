import Proof.Quartic.Cells.Parameters

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params`, paper/paper.tex: all finite selection
rules satisfied by a successful computation of the public parameters. -/
structure ParameterRules (x : ParameterInput) (p : Parameters) : Prop where
  input_valid : ValidInput x
  lambda_eq : p.lambda = NearCubicGates.Target.lambda x.n
  mu_eq : p.mu = NearCubicGates.Target.mu x.n
  m_eq : p.m = 4
  r_eq : p.r = 16 * p.mu
  r_bound : 4 * p.r ≤ x.n
  s_eq : p.s = Nat.log 2 (x.n / p.r + 1)
  b_eq : p.b = 2 ^ p.s - 1
  k_eq : p.k = p.r * p.s
  N_eq : p.N = 2 ^ (p.k / 2)
  Jmax_eq : p.Jmax = p.mu + 1
  T_eq : p.T = concentrationT p.m p.k p.Jmax x.beta
  tau_eq : p.tau = p.k + ceilLog 2 (16 / x.beta)
  U_eq : p.U = max p.tau (ceilSqrtRat
    ((96 ^ 2 * (p.r : ℚ) ^ 3 * (x.W : ℚ) ^ 2) / (x.beta ^ 2 * (x.n : ℚ) ^ 3)))
  pi0_eq : p.pi0 = (p.tau : ℚ) / (4 * p.U)
  Xmax_eq : p.Xmax = ceilSqrt (9 * p.tau ^ 2 * x.n * p.r)
  dstar_eq : p.dstar = 2 * p.Xmax * p.U / (3 * p.r * p.tau)
  omega1_eq : p.omega1 = 4 * p.m * x.G1 + 1
  omega2_eq : p.omega2 = 4 * p.m * x.G2 + 1
  MF_eq : p.MF = ceilSqrt (p.omega1 * p.omega2)
  eta_eq : p.eta = x.beta / (16 * p.MF)
  Qexp_eq : p.Qexp = sampleExponent p.N p.m (2 * (p.omega1 * p.omega2)) p.eta
  Q_eq : p.Q = 2 ^ p.Qexp
  ellf_eq : p.ellf = max p.k (p.Qexp + 1)
  S_eq : p.S = 2 * p.m * p.ellf
  NatAtoms_eq : p.NatAtoms = (4 * p.m + 1) * (2 * x.n ^ 4)
  childCap_eq : p.childCap = childCap x.n (NearCubicGates.Close.Counter.B0 x.n)
  Uocc_eq : p.Uocc = 1 + p.NatAtoms * p.childCap
  initial_degree : DegreePass x.n p.m p.k p.Uocc 0
  Dmax_eq : p.Dmax = Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n
  BN_eq : p.BN = p.S + p.m * p.k + 2 * p.m * Nat.clog 2 (p.N ^ 2 * p.Q) + 1
  P_eq : p.P = Nat.findGreatest
    (PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax p.Dmax) x.n
  prime_candidate : PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax p.Dmax p.P
  e_eq : liftExponent p.BN p.P = some p.e
  moment_degree : 4 * p.m * p.Xmax + 2 * p.m * p.k ≤ p.Dmax
  primes_eq : p.primes = NearCubicGates.Close.Counter.dyadicPrimes p.P
  primes_nonempty : p.primes.Nonempty
  Dprime_eq : p.Dprime = NearCubicGates.ScalarWindow.window p.primes
  L2_eq : p.L2 = NearCubicGates.Close.Counter.pairSide p.Dprime
  Lw_eq : p.Lw = NearCubicGates.Close.Counter.windowInUse x.pair p.L2 p.Dprime
  hE_eq : p.hE = p.P / 4
  h_eq : p.h = p.hE / (2 * p.m)
  height : 64 * p.T ≤ p.h
  ell0_eq : p.ell0 = (32 * p.m * p.U : ℕ)
  M1_eq : p.M1 = NearCubicGates.Close.Counter.firstDen p.ell0 p.h p.T
  chain_eq : NearCubicGates.Close.Counter.stopIndex
    (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) x.n = some (p.J - 1)
  J_pos : 1 ≤ p.J
  J_bound : p.J ≤ p.Jmax
  factors_eq : p.factors = NearCubicGates.Close.Counter.chainFactors
    (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) (p.J - 1)
  A_eq : p.A = p.factors.prod
  Lambda_eq : p.Lambda = (p.Lw - 1) * p.A / 2 + 1

/-- `sec:params`, paper/paper.tex: a successful exact
parameter computation satisfies every finite rule and every failure guard. -/
theorem prepare_spec (x : ParameterInput) (p : Parameters) (hs : prepare x = some p) :
    ParameterRules x p := by
  unfold prepare at hs
  simp only at hs
  split at hs
  swap
  · cases hs
  rename_i hv
  split at hs
  swap
  · cases hs
  rename_i hr
  split at hs
  swap
  · cases hs
  rename_i hd
  split at hs
  swap
  · cases hs
  rename_i hp
  split at hs
  · cases hs
  rename_i e he
  split at hs
  swap
  · cases hs
  rename_i hm
  split at hs
  swap
  · cases hs
  rename_i hpr
  split at hs
  swap
  · cases hs
  rename_i hh
  split at hs
  · cases hs
  rename_i Jlean hJ
  split at hs
  swap
  · cases hs
  rename_i hJb
  cases hs
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
    initial_degree := hd
    Dmax_eq := rfl
    BN_eq := rfl
    P_eq := rfl
    prime_candidate := hp
    e_eq := he
    moment_degree := hm
    primes_eq := rfl
    primes_nonempty := hpr
    Dprime_eq := rfl
    L2_eq := rfl
    Lw_eq := rfl
    hE_eq := rfl
    h_eq := rfl
    height := hh
    ell0_eq := rfl
    M1_eq := rfl
    chain_eq := by simpa using hJ
    J_pos := Nat.le_add_left 1 Jlean
    J_bound := hJb
    factors_eq := by simp
    A_eq := rfl
    Lambda_eq := rfl }

end NearQuarticWires.Cells
