import Proof.Quartic.StageCert.NewtonSetup

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the nonzero
Newton branch computes its exact binomial magnitude and canonical parity. -/
def activeNewton : St VV MM :=
  .seq prepareNewtonBinomial (.seq exactBinomial finishNewtonBinomial)

/-- `lem:maskpoly`, paper/paper.tex: the exact
coefficient computation changes only its private recurrence and result fields. -/
def newtonScratch : List (Fin VV) :=
  [chooseN,chooseR,newtonSignField,newtonMagnitudeField,newtonDifference,newtonHalf]++binomialScratch

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: a nonvanishing original Newton coefficient is generated
with its full integer sign in linearly many bounded binary operations. -/
theorem activeNewton_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (tau index : ℕ)
    (ht : a.env newtonTau=tau) (hi : a.env newtonIndex=index) (hactive : tau < index)
    (hwidth : 2*index+2≤C.Wd) :
    Hs C activeNewton a (17*tau+22) (fun z=>
      z.env newtonMagnitudeField=(index-1).choose tau ∧
      z.env newtonSignField=(index-tau)%2 ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z newtonScratch) := by
  have hcap := binomial_capacity_of_width (index-1) C.Wd (by omega)
  unfold activeNewton
  apply Hx.hs
  refine Hs.then (prepareNewtonBinomial_run C a hc tau index ht hi (by omega))
    (fun b ⟨bn,br,bsh,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (exactBinomial_run C b bc (index-1) tau bn br hcap.1 hcap.2)
    (fun d ⟨dv,dsh,dc,dfr⟩ n2 hn2=>?_)
  have dt : d.env newtonTau=tau := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans ht)
  have di : d.env newtonIndex=index := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans hi)
  refine Hs.last (finishNewtonBinomial_run C d dc tau index dt di dv (by omega) (by omega))
    (fun z ⟨zm,zs,zsh,zc,zfr⟩ n3 hn3=>?_)
  refine ⟨⟨zm,zs,zsh.trans (dsh.trans bsh),zc,?_⟩,?_⟩
  · exact (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (zfr.weaken (by decide)))
  · rw [min_eq_right (show tau ≤ index-1 by omega)] at hn2
    omega

end NearQuarticWires.StageCert.Tokens
