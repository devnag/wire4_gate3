import Proof.Quartic.Cells.ParametersArithmetic
import Proof.Quartic.Cells.Children

set_option autoImplicit false

namespace NearQuarticWires.Cells

open ParameterArithmetic

/-- `sec:params`, paper/paper.tex: all public data used by
the parameter computation, independent of the counting witness. -/
structure ParameterInput where
  n : ℕ
  W : ℕ
  G1 : ℕ
  G2 : ℕ
  beta : ℚ
  pair : Bool

/-- `sec:params`, paper/paper.tex: the parameters selected
by the exact finite rules, including the rational rate chain. -/
structure Parameters where
  lambda : ℕ
  mu : ℕ
  m : ℕ
  r : ℕ
  s : ℕ
  b : ℕ
  k : ℕ
  N : ℕ
  Jmax : ℕ
  T : ℕ
  tau : ℕ
  U : ℕ
  Xmax : ℕ
  dstar : ℕ
  omega1 : ℕ
  omega2 : ℕ
  MF : ℕ
  Q : ℕ
  ellf : ℕ
  S : ℕ
  NatAtoms : ℕ
  childCap : ℕ
  Uocc : ℕ
  Dmax : ℕ
  BN : ℕ
  P : ℕ
  e : ℕ
  hE : ℕ
  h : ℕ
  Lw : ℕ
  pi0 : ℚ
  eta : ℚ
  Qexp : ℕ
  primes : Finset ℕ
  Dprime : ℕ
  L2 : ℕ
  M1 : ℕ
  J : ℕ
  A : ℕ
  Lambda : ℕ
  ell0 : ℚ
  factors : List ℕ

namespace ParameterArithmetic

/-- `sec:params`, paper/paper.tex: nonconstant normalized
calls satisfying the public wire and precision bounds. -/
def ValidInput (x : ParameterInput) : Prop :=
  4 ≤ x.n ∧ 0 < x.W ∧ x.G1 + x.G2 ≤ x.W ∧ x.W ≤ 2 * x.n ^ 4 ∧
    0 < x.beta ∧ x.beta ≤ 1 / 16 ∧ (x.pair = false → x.G2 = 0)

instance (x : ParameterInput) : Decidable (ValidInput x) := by
  unfold ValidInput
  infer_instance

/-- `sec:params`, paper/paper.tex: the exact printing
degree comparison, including the fixed factor one hundred. -/
def DegreePass (n m k Uocc D : ℕ) : Prop :=
  100 * (m * k + 2 + D * Nat.clog 2 Uocc) ≤ n - k

instance (n m k Uocc : ℕ) : DecidablePred (DegreePass n m k Uocc) := fun D => by
  unfold DegreePass
  infer_instance

/-- `eq:prime-budget`, paper/paper.tex: a finite prime-scale
candidate with the least positive lift exponent and the mask-degree charge. -/
def PrimeCandidate (n BN Jmax m Xmax Dmax P : ℕ) : Prop :=
  100 ≤ P ∧ P ≤ n ∧
    match liftExponent BN P with
    | none => False
    | some e => (2 * e - 1) * (2 * Jmax + 2) * (P - 1) + 4 * m * Xmax ≤ Dmax

instance (n BN Jmax m Xmax Dmax : ℕ) :
    DecidablePred (PrimeCandidate n BN Jmax m Xmax Dmax) := fun P => by
  unfold PrimeCandidate
  cases liftExponent BN P <;> infer_instance

end ParameterArithmetic

/-- `sec:params`, paper/paper.tex: the exact finite parameter
computation. A failed public guard returns `none`; constant calls are evaluated
separately. Square and fourth roots use integer-power comparisons, and the rate
chain is imported from `Proof.Gates.Counter.Params`. -/
def prepare (x : ParameterInput) : Option Parameters :=
  if ValidInput x then
    let lam := NearCubicGates.Target.lambda x.n
    let mu := NearCubicGates.Target.mu x.n
    let m := 4
    let r := 16 * mu
    if 4 * r ≤ x.n then
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
      let theta := omega1 * omega2
      let I := 2 * theta
      let MF := ceilSqrt theta
      let eta := x.beta / (16 * MF)
      let Qexp := sampleExponent N m I eta
      let Q := 2 ^ Qexp
      let ellf := max k (Qexp + 1)
      let S := 2 * m * ellf
      let NatAtoms := (4 * m + 1) * (2 * x.n ^ 4)
      let cap := childCap x.n (NearCubicGates.Close.Counter.B0 x.n)
      let Uocc := 1 + NatAtoms * cap
      if DegreePass x.n m k Uocc 0 then
        let Dmax := Nat.findGreatest (DegreePass x.n m k Uocc) x.n
        let BN := S + m * k + 2 * m * Nat.clog 2 (N ^ 2 * Q) + 1
        let P := Nat.findGreatest (PrimeCandidate x.n BN Jmax m Xmax Dmax) x.n
        if PrimeCandidate x.n BN Jmax m Xmax Dmax P then
          match liftExponent BN P with
          | none => none
          | some e =>
            if 4 * m * Xmax + 2 * m * k ≤ Dmax then
              let primes := NearCubicGates.Close.Counter.dyadicPrimes P
              if primes.Nonempty then
                let Dprime := NearCubicGates.ScalarWindow.window primes
                let L2 := NearCubicGates.Close.Counter.pairSide Dprime
                let Lw := NearCubicGates.Close.Counter.windowInUse x.pair L2 Dprime
                let hE := P / 4
                let h := hE / (2 * m)
                if 64 * T ≤ h then
                  let ell0 : ℚ := (32 * m * U : ℕ)
                  let ratio := NearCubicGates.Close.Counter.firstRatio ell0 h T
                  match NearCubicGates.Close.Counter.stopIndex ratio x.n with
                  | none => none
                  | some Jlean =>
                    let J := Jlean + 1
                    if J ≤ Jmax then
                      let factors := NearCubicGates.Close.Counter.chainFactors ratio Jlean
                      let A := factors.prod
                      some {
                        lambda := lam, mu := mu, m := m, r := r, s := s, b := b,
                        k := k, N := N, Jmax := Jmax, T := T, tau := tau, U := U,
                        Xmax := Xmax, dstar := dstar, omega1 := omega1, omega2 := omega2,
                        MF := MF, Q := Q, ellf := ellf, S := S, NatAtoms := NatAtoms,
                        childCap := cap, Uocc := Uocc, Dmax := Dmax, BN := BN, P := P,
                        e := e, hE := hE, h := h, Lw := Lw, pi0 := pi0, eta := eta,
                        Qexp := Qexp, primes := primes, Dprime := Dprime, L2 := L2,
                        M1 := NearCubicGates.Close.Counter.firstDen ell0 h T, J := J,
                        A := A, Lambda := (Lw - 1) * A / 2 + 1, ell0 := ell0,
                        factors := factors }
                    else none
                else none
              else none
            else none
        else none
      else none
    else none
  else none

end NearQuarticWires.Cells
