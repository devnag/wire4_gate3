import Proof.Quartic.Cells.ParametersSpec

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: the public scale identities, without the later degree, prime
or rate-chain acceptance conditions. -/
structure CoreRules (x : ParameterInput) (p : Parameters) : Prop where
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
  BN_eq : p.BN = p.S + p.m * p.k + 2 * p.m * Nat.clog 2 (p.N ^ 2 * p.Q) + 1

/-- `sec:params`, paper/paper.tex: every fully selected
parameter record satisfies the public scale identities. -/
instance (x : ParameterInput) (p : Parameters) : Coe (ParameterRules x p) (CoreRules x p) where
  coe hs := {
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
    BN_eq := hs.BN_eq
  }

end NearQuarticWires.Cells
