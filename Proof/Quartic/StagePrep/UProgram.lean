import Proof.Quartic.StagePrep.UExpressions
import Proof.Quartic.StagePrep.RationalCeil
import Proof.Quartic.StagePrep.CeilSqrt
import Proof.Quartic.StagePrep.MaxRegister

/-!
# Physical computation of the incidence bound

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The exact incidence-bound computation of `sec:params`,
paper/paper.tex, uses integer products, a rational
ceiling, the canonical square-root ceiling, and one maximum. -/
def uProgram : St VV :=
  .seq (assign rationalNumReg uNumeratorExpression)
    (.seq (assign rationalDenReg uDenominatorExpression)
      (.seq rationalCeilProgram (.seq (.op (.copy SQX rationalCeilReg))
        (.seq ceilSqrtProgram (maxRegister pU tauReg SQS)))))

/-- The exact natural root argument for `U` in `sec:params`,
paper/paper.tex. -/
def uRootArgument (n r W num den : ℕ) : ℕ :=
  ⌈((uNumerator r W den : ℕ) : ℚ) / uDenominator n num⌉₊

/-- The computation of `sec:params`, paper/paper.tex, writes the canonical `U` using no later parameter
success assumption. -/
theorem uProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n r W num den tau : ℕ) (beta : ℚ)
    (hnv : a.env vN = n) (hrv : a.env rReg = r) (hWv : a.env pW = W)
    (huv : a.env vNUM = num) (hdv : a.env vDEN = den) (htv : a.env tauReg = tau)
    (hbn : beta.num = num) (hbd : beta.den = den)
    (hn : 0 < n) (hr : 0 < r) (hW : 0 < W) (hu : 0 < num) (hd : 0 < den)
    (hratio : uNumerator r W den + 2 * uDenominator n num + 4 < 2 ^ C.Wd)
    (hroot : uRootArgument n r W num den * uRootArgument n r W num den +
      uRootArgument n r W num den + 3 < 2 ^ C.Wd) :
    Hs C uProgram a (20 * uRootArgument n r W num den + 20000) (fun b =>
      b.env pU = max tau (Cells.ParameterArithmetic.ceilSqrtRat
        ((96 ^ 2 * (r : ℚ) ^ 3 * (W : ℚ) ^ 2) / (beta ^ 2 * (n : ℚ) ^ 3))) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [rationalNumReg, rationalDenReg, rationalCeilReg,
        SQX, SQS, SQF, SQT, SQU, pU, vJ]) := by
  have hdenpos := (uDenominator_parts n num hn hu).1
  have hrootEq : Cells.ParameterArithmetic.ceilSqrtRat
      ((96 ^ 2 * (r : ℚ) ^ 3 * (W : ℚ) ^ 2) / (beta ^ 2 * (n : ℚ) ^ 3)) =
      Cells.ParameterArithmetic.ceilSqrt (uRootArgument n r W num den) := by
    rw [u_ratio_encoding n r W num den beta hbn hbd hn hu hd]
    rfl
  unfold uProgram
  refine Hx.hs (Hs.then (assign_spec rationalNumReg (by decide) (by decide)
    uNumeratorExpression a (by unfold uNumeratorExpression; aevar)
    (by unfold uNumeratorExpression; aevar) hc
    (uNumeratorExpression_ok a C.Wd r W den hrv hWv hdv hr hW hd (by omega)))
    (fun b ⟨hbnumer, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbnumer' : b.env rationalNumReg = uNumerator r W den := by
    simpa only [uNumeratorExpression, AE.eval, hrv, hWv, hdv, uNumerator] using hbnumer
  have hbnv : b.env vN = n := (hbfr _ (by decide) (by decide) (by decide)).trans hnv
  have hbuv : b.env vNUM = num := (hbfr _ (by decide) (by decide) (by decide)).trans huv
  refine Hs.then (assign_spec rationalDenReg (by decide) (by decide)
    uDenominatorExpression b (by unfold uDenominatorExpression; aevar)
    (by unfold uDenominatorExpression; aevar) hbc
    (uDenominatorExpression_ok b C.Wd n num hbnv hbuv hn hu (by omega)))
    (fun d ⟨hdden, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hdden' : d.env rationalDenReg = uDenominator n num := by
    simpa only [uDenominatorExpression, AE.eval, hbnv, hbuv, uDenominator] using hdden
  have hdA : d.env rationalNumReg = uNumerator r W den :=
    (hdfr _ (by decide) (by decide) (by decide)).trans hbnumer'
  refine Hs.then (rationalCeilProgram_spec C d hdc _ _ hdA hdden' hdenpos hratio)
    (fun e ⟨hearg, hecp, hewq, heout, hec, hefr⟩ n3 hn3 => ?_)
  have hearg' : e.env rationalCeilReg = uRootArgument n r W num den := hearg
  refine Hs.then (hs_copy C SQX rationalCeilReg e (by decide)) (fun f hf n4 hn4 => ?_)
  subst hf
  have hfc : Cst (e.set SQX (e.env rationalCeilReg)) := hec.set _ _ (by decide)
  refine Hs.then (ceilSqrtProgram_spec C _ hfc _
    (by rw [DS.set_env_self, hearg']) hroot)
    (fun g ⟨hgroot, hgcp, hgwq, hgout, hgc, hgfr⟩ n5 hn5 => ?_)
  have hgtau : g.env tauReg = tau := by
    rw [hgfr _ (by decide), DS.set_env_ne _ _ (by decide),
      hefr _ (by decide) (by decide), hdfr _ (by decide) (by decide) (by decide),
      hbfr _ (by decide) (by decide) (by decide), htv]
  refine Hs.last (maxRegister_spec C pU tauReg SQS (by decide) (by decide)
    (by decide) (by decide) g hgc)
    (fun h ⟨hhU, hhcp, hhwq, hhout, hhc, hhfr⟩ n6 hn6 => ?_)
  refine ⟨⟨?_, hhcp.trans (hgcp.trans (hecp.trans (hdcp.trans hbcp))),
    hhwq.trans (hgwq.trans (hewq.trans (hdwq.trans hbwq))),
    hhout.trans (hgout.trans (heout.trans (hdout.trans hbout))), hhc, ?_⟩, ?_⟩
  · rw [hhU, hgtau, hgroot, hrootEq]
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (FrS.weaken hefr (by decide))
          (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
            (FrS.trans (FrS.weaken hgfr.toS (by decide)) (FrS.weaken hhfr.toS (by decide))))))
  · simp only [uNumeratorExpression, uDenominatorExpression, AE.cost] at hn1 hn2
    omega

end NearQuarticWires.StagePrep
