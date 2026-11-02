import Proof.Quartic.Cells.ParametersPublic

/-!
# Exact finite selection after the public scales

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open Cells.ParameterArithmetic

/-- The finite degree, prime and rate-chain tests in
`sec:params`, paper/paper.tex, consume the
already computed exact public scales. -/
def selectPublicParameters (x : Cells.ParameterInput) (p : Cells.Parameters) :
    Option Cells.Parameters :=
  if DegreePass x.n p.m p.k p.Uocc 0 then
    let Dmax := Nat.findGreatest (DegreePass x.n p.m p.k p.Uocc) x.n
    let P := Nat.findGreatest (PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax Dmax) x.n
    if PrimeCandidate x.n p.BN p.Jmax p.m p.Xmax Dmax P then
      match liftExponent p.BN P with
      | none => none
      | some e =>
        if 4 * p.m * p.Xmax + 2 * p.m * p.k ≤ Dmax then
          let primes := NearCubicGates.Close.Counter.dyadicPrimes P
          if primes.Nonempty then
            let Dprime := NearCubicGates.ScalarWindow.window primes
            let L2 := NearCubicGates.Close.Counter.pairSide Dprime
            let Lw := NearCubicGates.Close.Counter.windowInUse x.pair L2 Dprime
            let hE := P / 4
            let h := hE / (2 * p.m)
            if 64 * p.T ≤ h then
              let ell0 : ℚ := (32 * p.m * p.U : ℕ)
              let ratio := NearCubicGates.Close.Counter.firstRatio ell0 h p.T
              match NearCubicGates.Close.Counter.stopIndex ratio x.n with
              | none => none
              | some i =>
                let J := i + 1
                if J ≤ p.Jmax then
                  let factors := NearCubicGates.Close.Counter.chainFactors ratio i
                  let A := factors.prod
                  some {
                    p with
                    Dmax := Dmax
                    P := P
                    e := e
                    hE := hE
                    h := h
                    Lw := Lw
                    primes := primes
                    Dprime := Dprime
                    L2 := L2
                    M1 := NearCubicGates.Close.Counter.firstDen ell0 h p.T
                    J := J
                    A := A
                    Lambda := (Lw - 1) * A / 2 + 1
                    ell0 := ell0
                    factors := factors }
                else none
            else none
          else none
        else none
    else none
  else none

/-- The literal canonical computation in `sec:params`,
paper/paper.tex, equals the finite selection
from its complete public-scale record after the first guard. -/
theorem prepare_eq_selectPublicParameters (x : Cells.ParameterInput)
    (hv : ValidInput x)
    (hr : 4 * (16 * NearCubicGates.Target.mu x.n) ≤ x.n) :
    Cells.prepare x = selectPublicParameters x (Cells.publicScales x) := by
  unfold Cells.prepare
  rw [if_pos hv, if_pos hr]
  rfl

/-- The failed first guard of `sec:params`, paper/paper.tex, is exactly a failed canonical preparation. -/
theorem prepare_none_of_header_failure (x : Cells.ParameterInput)
    (hv : ValidInput x)
    (hr : ¬ 4 * (16 * NearCubicGates.Target.mu x.n) ≤ x.n) :
    Cells.prepare x = none := by
  unfold Cells.prepare
  rw [if_pos hv, if_neg hr]

end NearQuarticWires.StagePrep
