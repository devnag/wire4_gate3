import Proof.Quartic.StagePrep.AttemptParameters

/-!
# Exact identities on rejected and accepted attempts

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open Cells.ParameterArithmetic
open NearCubicGates.Close.Counter

/-- The identities computed in `sec:params`,
paper/paper.tex, without requiring any late
guard to succeed. Optional-result identities are asserted only
after their own literal existence guard. -/
structure AttemptRules (x : Cells.ParameterInput) (p : Cells.Parameters) : Prop
    extends Cells.CoreRules x p where
  Dmax_eq : p.Dmax=Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n
  P_eq : p.P=Nat.findGreatest (Cells.ParameterArithmetic.PrimeCandidate
    x.n p.BN p.Jmax p.m p.Xmax p.Dmax) x.n
  e_eq : Cells.ParameterArithmetic.PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax p.Dmax p.P →
    liftExponent p.BN p.P=some p.e
  primes_eq : p.primes=dyadicPrimes p.P
  Dprime_eq : p.Dprime=NearCubicGates.ScalarWindow.window p.primes
  L2_eq : p.L2=pairSide p.Dprime
  Lw_eq : p.Lw=windowInUse x.pair p.L2 p.Dprime
  hE_eq : p.hE=p.P/4
  h_eq : p.h=p.hE/(2*p.m)
  ell0_eq : p.ell0=(32*p.m*p.U:ℕ)
  M1_eq : p.M1=firstDen p.ell0 p.h p.T
  chain_eq : (stopIndex (firstRatio p.ell0 p.h p.T) x.n).isSome=true →
    stopIndex (firstRatio p.ell0 p.h p.T) x.n=some (p.J-1)
  J_pos : 1≤p.J
  J_bound : (stopIndex (firstRatio p.ell0 p.h p.T) x.n).isSome=true → p.J≤p.Jmax
  factors_eq : p.factors=chainFactors (firstRatio p.ell0 p.h p.T) (p.J-1)
  A_eq : p.A=p.factors.prod
  Lambda_eq : p.Lambda=(p.Lw-1)*p.A/2+1

/-- The total attempt of `sec:params`, paper/paper.tex, satisfies every computed identity on all
guard outcomes, retaining all early public information. -/
theorem attemptPublicParameters_rules (x : Cells.ParameterInput) (p : Cells.Parameters)
    (hs : Cells.CoreRules x p) : AttemptRules x (attemptPublicParameters x p) := by
  let q := attemptPublicParameters x p
  have hc : Cells.CoreRules x q := attemptPublicParameters_core x p hs
  have hJ : q.J=(stopIndex (firstRatio q.ell0 q.h q.T) x.n).getD 0+1 := rfl
  have he : q.e=(liftExponent q.BN q.P).getD 0 := rfl
  have hJmax : q.Jmax=Jmax x.n := by rw [hc.Jmax_eq,hc.mu_eq]; rfl
  have hchain : (stopIndex (firstRatio q.ell0 q.h q.T) x.n).isSome=true →
      stopIndex (firstRatio q.ell0 q.h q.T) x.n=some (q.J-1) := by
    intro hon
    cases hz : stopIndex (firstRatio q.ell0 q.h q.T) x.n with
    | none => rw [hz] at hon; cases hon
    | some i =>
      have hJi : q.J=i+1 := by rw [hJ,hz]; rfl
      simp only [hJi,Nat.add_sub_cancel_right]
  refine {
    toCoreRules := hc
    Dmax_eq := rfl
    P_eq := rfl
    e_eq := ?_
    primes_eq := rfl
    Dprime_eq := rfl
    L2_eq := rfl
    Lw_eq := rfl
    hE_eq := rfl
    h_eq := rfl
    ell0_eq := rfl
    M1_eq := rfl
    chain_eq := hchain
    J_pos := by rw [hJ]; omega
    J_bound := ?_
    factors_eq := rfl
    A_eq := rfl
    Lambda_eq := rfl }
  · intro hpc
    rw [he]
    cases hz : liftExponent q.BN q.P with
    | none =>
      have hcheck := hpc.2.2
      rw [hz] at hcheck
      exact hcheck.elim
    | some e => rfl
  · intro hon
    change q.J≤q.Jmax
    have hz := hchain hon
    have hbound : q.J-1≤Jmax x.n-1 :=
      (leastUpTo_spec _ _ _ hz).2.1
    rw [←hJmax] at hbound
    have hpos : 1≤q.J := by rw [hJ]; omega
    have hmaxpos : 1≤q.Jmax := by rw [hc.Jmax_eq]; omega
    omega

/-- The complete canonical computation of `sec:params`,
paper/paper.tex, has one total finite attempt
record and its exact conjunction of public guard outcomes. -/
theorem prepare_eq_attempt (x : Cells.ParameterInput) (hv : ValidInput x)
    (hr : 4*(16*NearCubicGates.Target.mu x.n)≤x.n) :
    Cells.prepare x =
      if attemptPass x (attemptPublicParameters x (Cells.publicScales x)) then
        some (attemptPublicParameters x (Cells.publicScales x)) else none := by
  rw [prepare_eq_selectPublicParameters x hv hr,selectPublicParameters_eq_attempt]

/-- A rejected parameter selection in `sec:params`,
paper/paper.tex, is precisely a failed literal
guard of the total finite attempt record. -/
theorem prepare_none_iff_attempt_failure (x : Cells.ParameterInput) (hv : ValidInput x)
    (hr : 4*(16*NearCubicGates.Target.mu x.n)≤x.n) :
    Cells.prepare x=none ↔ ¬attemptPass x (attemptPublicParameters x (Cells.publicScales x)) := by
  rw [prepare_eq_attempt x hv hr]
  split <;> simp_all

/-- A selected parameter record of `sec:params`,
paper/paper.tex, equals the total finite
attempt on all of its fields, including both literal lists. -/
theorem prepare_some_eq_attempt (x : Cells.ParameterInput) (hv : ValidInput x)
    (hr : 4*(16*NearCubicGates.Target.mu x.n)≤x.n) (p : Cells.Parameters)
    (hp : Cells.prepare x=some p) :
    p=attemptPublicParameters x (Cells.publicScales x) := by
  rw [prepare_eq_attempt x hv hr] at hp
  split at hp
  · exact (Option.some.inj hp).symm
  · cases hp

end NearQuarticWires.StagePrep
