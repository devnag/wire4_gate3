import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.UArithmetic
import Proof.Gates.Dispatch.ParamsB

/-!
# The integer product expressions for the incidence bound

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The numerator expression for `sec:params`, paper/paper.tex. -/
def uNumeratorExpression : AE :=
  mul (mul (mul (lit 9216) (mul (mul (var rReg) (var rReg)) (var rReg)))
    (mul (var pW) (var pW))) (mul (var vDEN) (var vDEN))

/-- The denominator expression for `sec:params`, paper/paper.tex. -/
def uDenominatorExpression : AE :=
  mul (mul (var vNUM) (var vNUM)) (mul (mul (var vN) (var vN)) (var vN))

/-- All physical numerator intermediates for `sec:params`,
paper/paper.tex, fit whenever its actual positive
product fits the register width. -/
theorem uNumeratorExpression_ok (a : DS VV) (Wd r W den : ℕ)
    (hrv : a.env rReg = r) (hWv : a.env pW = W) (hdv : a.env vDEN = den)
    (hr : 0 < r) (hW : 0 < W) (hd : 0 < den)
    (hcap : uNumerator r W den < 2 ^ Wd) :
    uNumeratorExpression.ok Wd a.env := by
  obtain ⟨hc, hr2, hr3, hW2, hd2, hp, hp2⟩ := uNumerator_parts r W den hr hW hd
  have hc' := hc.trans_lt hcap
  have hr2' := hr2.trans_lt hcap
  have hr3' := hr3.trans_lt hcap
  have hW2' := hW2.trans_lt hcap
  have hd2' := hd2.trans_lt hcap
  have hp' := hp.trans_lt hcap
  have hp2' := hp2.trans_lt hcap
  unfold uNumerator at hcap
  unfold uNumeratorExpression
  aeok [hrv, hWv, hdv]

/-- All physical denominator intermediates for `sec:params`,
paper/paper.tex, fit whenever its actual positive
product fits the register width. -/
theorem uDenominatorExpression_ok (a : DS VV) (Wd n num : ℕ)
    (hnv : a.env vN = n) (huv : a.env vNUM = num)
    (hn : 0 < n) (hu : 0 < num)
    (hcap : uDenominator n num < 2 ^ Wd) :
    uDenominatorExpression.ok Wd a.env := by
  obtain ⟨_, hu2, hn2, hn3⟩ := uDenominator_parts n num hn hu
  have hu2' := hu2.trans_lt hcap
  have hn2' := hn2.trans_lt hcap
  have hn3' := hn3.trans_lt hcap
  unfold uDenominator at hcap
  unfold uDenominatorExpression
  aeok [hnv, huv]

end NearQuarticWires.StagePrep
