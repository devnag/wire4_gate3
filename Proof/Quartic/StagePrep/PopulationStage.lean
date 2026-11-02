import Proof.Quartic.StagePrep.XMaxProgram
import Proof.Quartic.StagePrep.DStarProgram

/-!
# The complete population-bound computation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The consecutive residual and incidence-cutoff computations
of `sec:params`, paper/paper.tex. -/
def populationStage : St VV := .seq xMaxProgram dStarProgram

/-- Both population fields of `sec:params`, paper/paper.tex, are retained by the complete actual integer
computation before any later acceptance guard. -/
theorem populationStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n r tau U : ℕ) (hnv : a.env vN = n) (hrv : a.env rReg = r)
    (htv : a.env tauReg = tau) (hUv : a.env pU = U)
    (hn : 0 < n) (hr : 0 < r) (ht : 0 < tau) (hU : 0 < U)
    (hroot : xMaxArgument n r tau * xMaxArgument n r tau +
      xMaxArgument n r tau + 3 < 2 ^ C.Wd)
    (hcut : 2 * Cells.ParameterArithmetic.ceilSqrt (9 * tau ^ 2 * n * r) * U +
      6 * r * tau + 16 < 2 ^ C.Wd) :
    Hs C populationStage a (20 * xMaxArgument n r tau + 158) (fun b =>
      b.env xMaxReg = Cells.ParameterArithmetic.ceilSqrt (9 * tau ^ 2 * n * r) ∧
      b.env dStarReg = 2 * Cells.ParameterArithmetic.ceilSqrt (9 * tau ^ 2 * n * r) * U /
        (3 * r * tau) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [SQX, SQS, SQF, SQT, SQU, xMaxReg, dStarReg, vJ]) := by
  unfold populationStage
  refine Hx.hs (Hs.then (xMaxProgram_spec C a hc n r tau hnv hrv htv hn hr ht hroot)
    (fun b ⟨hbX, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbU : b.env pU = U := (hbfr _ (by decide) (by decide)).trans hUv
  have hbr : b.env rReg = r := (hbfr _ (by decide) (by decide)).trans hrv
  have hbt : b.env tauReg = tau := (hbfr _ (by decide) (by decide)).trans htv
  refine Hs.last (dStarProgram_spec C b hbc _ U r tau hbX hbU hbr hbt hU hr ht hcut) ?_
  rintro d ⟨hdd, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2
  refine ⟨⟨?_, hdd, hdcp.trans hbcp, hdwq.trans hbwq, hdout.trans hbout,
    hdc, FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr (by decide))⟩, by omega⟩
  exact (hdfr _ (by decide) (by decide)).trans hbX

end NearQuarticWires.StagePrep
