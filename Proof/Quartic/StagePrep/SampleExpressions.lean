import Proof.Quartic.StagePrep.SampleArithmetic
import Proof.Quartic.StagePrep.PositiveProducts
import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# The positive products in the sampling comparison

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The literal numerator expression of the sample test in
`sec:params`, paper/paper.tex. -/
def sampleNumeratorExpression : AE :=
  mul (mul (powerExpression (mul (mul (lit 1024) (var nSideReg)) (var mReg)) 4)
    (mul (mul (mul (lit 8) (var nSideReg)) (var nSideReg))
      (mul (var omegaOneReg) (var omegaTwoReg))))
    (powerExpression (var etaDenReg) 8)

/-- The literal denominator expression of the sample test in
`sec:params`, paper/paper.tex. -/
def sampleDenominatorExpression : AE := powerExpression (var etaNumReg) 8

/-- The numerator expression of `sec:params`, paper/paper.tex, evaluates to its exact integer product. -/
theorem sampleNumeratorExpression_eval (a : DS VV) (N m o1 o2 den : ℕ)
    (hN : a.env nSideReg = N) (hm : a.env mReg = m)
    (ho1 : a.env omegaOneReg = o1) (ho2 : a.env omegaTwoReg = o2)
    (hd : a.env etaDenReg = den) :
    sampleNumeratorExpression.eval a.env = sampleNumerator N m (o1 * o2) den := by
  simp only [sampleNumeratorExpression, AE.eval, powerExpression_eval,
    hN, hm, ho1, ho2, hd, sampleNumerator]

/-- The numerator expression of `sec:params`, paper/paper.tex, has only positive product factors. -/
theorem sampleNumeratorExpression_positive (a : DS VV)
    (hN : 0 < a.env nSideReg) (hm : 0 < a.env mReg)
    (ho1 : 0 < a.env omegaOneReg) (ho2 : 0 < a.env omegaTwoReg)
    (hd : 0 < a.env etaDenReg) : PositiveProduct a.env sampleNumeratorExpression := by
  simp [sampleNumeratorExpression, PositiveProduct, powerExpression, hN, hm, ho1, ho2, hd]

end NearQuarticWires.StagePrep
