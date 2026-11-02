import Proof.Quartic.Cells.ParametersCompatibility
import Proof.Quartic.Algorithm.Parameters

set_option autoImplicit false

namespace NearQuarticWires.Cells

/-- `sec:params`, paper/paper.tex: express the selected
parameters in the notation used by the counting algorithm. -/
def toAlgorithmParameters (x : ParameterInput) (p : Parameters)
    (hs : ParameterRules x p) : Algorithm.Parameters where
  lam := p.lambda
  mu := p.mu
  m := p.m
  r := p.r
  s := p.s
  b := p.b
  k := p.k
  N := p.N
  Jmax := p.Jmax
  T := p.T
  tau := p.tau
  U := p.U
  pi0 := p.pi0
  Xmax := p.Xmax
  dstar := p.dstar
  Omega₁ := p.omega1
  Omega₂ := p.omega2
  Theta := p.omega1 * p.omega2
  I := 2 * (p.omega1 * p.omega2)
  MF := p.MF
  eta := p.eta
  Q := p.Q
  lf := p.ellf
  S := p.S
  Nat_ := p.NatAtoms
  mc := p.childCap
  Uocc := p.Uocc
  Dmax := p.Dmax
  BN := p.BN
  P := p.P
  e := p.e
  primes := p.primes
  Dprime := p.Dprime
  L2 := p.L2
  Lw := p.Lw
  hE := p.hE
  h := p.h
  ell0 := 32 * p.m * p.U
  ellBar := NearCubicGates.Close.Counter.ellBar p.ell0 p.h p.T
  M1 := p.M1
  J := p.J
  rate := fun i => NearCubicGates.RationalRateChain.factorRat
    (NearCubicGates.RationalRateChain.ratio
      (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i)
  A := p.A
  Lambda := p.Lambda
  eta_pos := hs.eta_pos
  budget := by
    have h := hs.sample_budget
    rw [hs.m_eq] at h
    convert h using 1
    push_cast
    ring
  primes_prime := fun q hq => (hs.selected_prime_guards q hq).1
  primes_nonempty := hs.primes_nonempty
  width := fun q hq => by have h := (hs.selected_prime_guards q hq).2; omega
  Dprime_eq := hs.Dprime_eq
  L2_eq := hs.L2_eq.trans (by rfl)
  Lambda_eq := hs.Lambda_eq
  box := by rw [hs.Lambda_eq]; omega
  m_eq := hs.m_eq
  k_even := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp hs.k_even)
  N_eq := hs.N_eq
  S_eq := hs.S_eq
  BN_eq := hs.BN_eq
  P_ge := hs.prime_maximal.1
  e_eq := (ParameterArithmetic.algorithm_primeExponent_eq p.BN p.P p.e
    (by have := hs.prime_maximal.1; omega) hs.e_eq).symm
  primes_gt := fun q hq => by
    rw [hs.primes_eq, NearCubicGates.Close.Counter.mem_dyadicPrimes] at hq
    exact hq.2.2
  pair := x.pair
  Lw_eq := hs.Lw_eq
  A_pos := hs.A_pos

/-- `sec:params`, paper/paper.tex: the
three plan outcomes, using the exact parameter computation. -/
def preparedPlan (x : ParameterInput) : Algorithm.Plan :=
  if x.n < 4 then .soundDefault
  else if x.W = 0 then .exactEvaluation
  else match hp : prepare x with
    | none => .soundDefault
    | some p => .run (toAlgorithmParameters x p (prepare_spec x p hp))

/-- `sec:params`, paper/paper.tex: every successful
parameter computation yields the corresponding counting-algorithm plan. -/
theorem preparedPlan_run (x : ParameterInput) (p : Parameters) (hp : prepare x = some p) :
    preparedPlan x = .run (toAlgorithmParameters x p (prepare_spec x p hp)) := by
  have hs := prepare_spec x p hp
  have hn : ¬ x.n < 4 := by have := hs.input_valid.1; omega
  have hw : x.W ≠ 0 := by have := hs.input_valid.2.1; omega
  simp only [preparedPlan, if_neg hn, if_neg hw]
  split
  · rename_i hnone
    rw [hp] at hnone
    cases hnone
  · rename_i q hq
    have hqp : q = p := by
      rw [hp] at hq
      exact (Option.some.inj hq).symm
    subst q
    rfl

namespace ParameterRules

variable {x : ParameterInput} {p : Parameters}

/-- `sec:params`, paper/paper.tex: the algorithm's
natural chain origin equals the selected rational chain origin after casting. -/
theorem algorithm_ell0 (hs : ParameterRules x p) :
    ((toAlgorithmParameters x p hs).ell0 : ℚ) = p.ell0 := hs.ell0_eq.symm

/-- `imp:chain` and `sec:params`, paper/paper.tex:
the algorithm's finite rate product is exactly the selected chain product. -/
theorem algorithm_rate_product (hs : ParameterRules x p) :
    (∏ i ∈ Finset.range (p.J - 1), (toAlgorithmParameters x p hs).rate i) = p.A := by
  rw [hs.A_eq, hs.factors_eq]
  simp only [toAlgorithmParameters, NearCubicGates.Close.Counter.chainFactors]
  simpa only [List.toFinset_range] using
    (List.prod_toFinset
      (fun i => NearCubicGates.RationalRateChain.factorRat
        (NearCubicGates.RationalRateChain.ratio
          (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i))
      List.nodup_range)

end ParameterRules
end NearQuarticWires.Cells
