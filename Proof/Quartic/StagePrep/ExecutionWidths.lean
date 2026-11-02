import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# Concrete word-capacity conditions for selected preparation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter

/-- Exact integer operand checks for the early rules of
`sec:params`, paper/paper.tex. These predicates
contain no execution or running-time assumption. -/
structure PublicScalesWidths (C : Ctx) (x : Cells.ParameterInput)
    (p : Cells.Parameters) (num den : ℕ) : Prop where
  dims : x.n*(x.n+1)+2*x.n+32 ≤ C.Wd
  cwidth : concentrationExponent p.m p.k < C.Wd
  cleft : 4*p.Jmax*2^concentrationExponent p.m p.k*den < 2^C.Wd
  cbound : 2^TBound (concentrationExponent p.m p.k) p.Jmax x.beta*num < 2^C.Wd
  cbits : TBound (concentrationExponent p.m p.k) p.Jmax x.beta+2 < C.Wd
  tauW : p.k+32*den+4*num+16 < 2^C.Wd
  uratio : uNumerator p.r x.W den+2*uDenominator x.n num+4 < 2^C.Wd
  uroot : uRootArgument x.n p.r x.W num den*uRootArgument x.n p.r x.W num den+
      uRootArgument x.n p.r x.W num den+3 < 2^C.Wd
  piW : 2*(p.tau+4*p.U)+4 < 2^C.Wd
  xroot : xMaxArgument x.n p.r p.tau*xMaxArgument x.n p.r p.tau+
      xMaxArgument x.n p.r p.tau+3 < 2^C.Wd
  xcut : 2*p.Xmax*p.U+6*p.r*p.tau+16 < 2^C.Wd
  fourier : fourierTheta p.m x.G1 x.G2*fourierTheta p.m x.G1 x.G2+
      fourierTheta p.m x.G1 x.G2+4*p.m+16 < 2^C.Wd
  etaW : 2*(num+16*p.MF*den)+4 < 2^C.Wd
  sample : 16*(sampleNumerator p.N p.m (p.omega1*p.omega2) p.eta.den+
      sampleDenominator p.eta.num.natAbs)+256 < 2^C.Wd
  Qexp : p.Qexp < C.Wd
  seed : 2*p.m*max p.k (p.Qexp+1)+p.k+p.Qexp+32 < 2^C.Wd

/-- Exact integer operand checks for the complete selected
computation of `sec:params`, paper/paper.tex.
The fields are fixed-word arithmetic inequalities, not an
assumed machine or a running-time certificate. -/
structure SelectedWidths (C : Ctx) (x : Cells.ParameterInput) (p : Cells.Parameters)
    (num den w1 w2 S : ℕ) : Prop where
  header : (3*x.n+4)*(x.n+1)+w1+w2+100*x.n+100 < 2^C.Wd
  early : PublicScalesWidths C x p num den
  print : p.NatAtoms*p.childCap+p.NatAtoms+p.childCap+2*x.n^4+
    (4*p.m+1)+(NearCubicGates.Close.Counter.B0 x.n+p.lambda+3)+128 < 2^C.Wd
  log : 2*p.Uocc+2 < 2^C.Wd
  degree : 100*(p.m*p.k+2+x.n*Nat.clog 2 p.Uocc)+x.n+p.k+256 < 2^C.Wd
  coefficient : 2*p.N*p.N*p.Q+p.S+p.m*p.k+
    2*p.m*Nat.clog 2 (p.N*p.N*p.Q)+2*p.m+32 < 2^C.Wd
  lift : 3*(p.BN-1)+4 < C.Wd
  powers : ∀ j≤2*p.BN, x.n^j < 2^C.Wd
  prime : primeDegreeMaximum p.BN x.n p.Jmax p.m p.Xmax+
    2*(p.BN+1)+(2*p.Jmax+2)+x.n+4*p.m+256 < 2^C.Wd
  moment : 4*p.m*p.Xmax+2*p.m*p.k+4*p.m+16 < 2^C.Wd
  primeCensus : 2*(p.P+1)*(p.P+1)+8 < 2^C.Wd
  pairWindow : 2*(p.Dprime*(p.Dprime*p.Dprime))+2*p.Dprime+8 < 2^C.Wd
  height : 32*p.m*p.U+4 < 2^C.Wd
  heightGuard : 64*p.T+128 < 2^C.Wd
  ell : 32*p.m*p.U < 2^S
  h : p.h < 2^S
  T : p.T < 2^S
  J : p.Jmax < 2^S
  chain : 6*S+40 ≤ C.Wd
  finish : p.Lw*p.A+(p.J-1)+8 < 2^C.Wd

/-- Exact operand checks through the last possible failing
search in `sec:params`, paper/paper.tex. These
conditions use no selected factor product or final success. -/
structure AttemptWidths (C : Ctx) (x : Cells.ParameterInput) (p : Cells.Parameters)
    (num den w1 w2 S : ℕ) : Prop where
  header : (3*x.n+4)*(x.n+1)+w1+w2+100*x.n+100 < 2^C.Wd
  early : PublicScalesWidths C x p num den
  print : p.NatAtoms*p.childCap+p.NatAtoms+p.childCap+2*x.n^4+
    (4*p.m+1)+(NearCubicGates.Close.Counter.B0 x.n+p.lambda+3)+128 < 2^C.Wd
  log : 2*p.Uocc+2 < 2^C.Wd
  degree : 100*(p.m*p.k+2+x.n*Nat.clog 2 p.Uocc)+x.n+p.k+256 < 2^C.Wd
  coefficient : 2*p.N*p.N*p.Q+p.S+p.m*p.k+
    2*p.m*Nat.clog 2 (p.N*p.N*p.Q)+2*p.m+32 < 2^C.Wd
  lift : 3*(p.BN-1)+4 < C.Wd
  powers : ∀ j≤2*p.BN, x.n^j < 2^C.Wd
  prime : primeDegreeMaximum p.BN x.n p.Jmax p.m p.Xmax+
    2*(p.BN+1)+(2*p.Jmax+2)+x.n+4*p.m+256 < 2^C.Wd
  moment : 4*p.m*p.Xmax+2*p.m*p.k+4*p.m+16 < 2^C.Wd
  primeCensus : 2*(p.P+1)*(p.P+1)+8 < 2^C.Wd
  pairWindow : 2*(p.Dprime*(p.Dprime*p.Dprime))+2*p.Dprime+8 < 2^C.Wd
  height : 32*p.m*p.U+4 < 2^C.Wd
  heightGuard : 64*p.T+128 < 2^C.Wd
  ell : 32*p.m*p.U < 2^S
  h : p.h < 2^S
  T : p.T < 2^S
  J : p.Jmax < 2^S
  chain : 6*S+40 ≤ C.Wd

end NearQuarticWires.StagePrep
