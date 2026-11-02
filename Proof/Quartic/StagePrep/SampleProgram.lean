import Proof.Quartic.StagePrep.SampleExpressions
import Proof.Quartic.StagePrep.ClogSixteen

/-!
# Physical computation of the sample-size exponent

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The sample-exponent computation of `sec:params`,
paper/paper.tex, contains only fixed products,
integer ceiling division, and the exact base-sixteen logarithm. -/
def sampleExponentProgram : St VV :=
  .seq (assign rationalNumReg sampleNumeratorExpression)
    (.seq (assign rationalDenReg sampleDenominatorExpression)
      (.seq rationalCeilProgram clogSixteenProgram))

/-- The program of `sec:params`, paper/paper.tex, computes the canonical sample exponent without
enumerating either the sample size or the integer quotient. -/
theorem sampleExponentProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (N m o1 o2 num den : ℕ) (eta : ℚ)
    (hNv : a.env nSideReg = N) (hmv : a.env mReg = m)
    (ho1v : a.env omegaOneReg = o1) (ho2v : a.env omegaTwoReg = o2)
    (huv : a.env etaNumReg = num) (hdv : a.env etaDenReg = den)
    (hun : eta.num = num) (hdd : eta.den = den)
    (hN : 0 < N) (hm : 0 < m) (ho1 : 0 < o1) (ho2 : 0 < o2)
    (hu : 0 < num) (hd : 0 < den)
    (hW : 16 * (sampleNumerator N m (o1 * o2) den + sampleDenominator num) + 256 < 2 ^ C.Wd) :
    Hs C sampleExponentProgram a
      (5 * Nat.clog 2 (sampleArgument N m (o1 * o2) num den) + 20000) (fun b =>
        b.env qExponentReg = Cells.ParameterArithmetic.sampleExponent N m (2 * (o1 * o2)) eta ∧
        b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
        FrS a b [rationalNumReg, rationalDenReg, rationalCeilReg,
          t3, t5, t6, qExponentReg, vJ]) := by
  have hpos := sampleNumeratorExpression_positive a
    (by rw [hNv]; exact hN) (by rw [hmv]; exact hm)
    (by rw [ho1v]; exact ho1) (by rw [ho2v]; exact ho2) (by rw [hdv]; exact hd)
  have heval := sampleNumeratorExpression_eval a N m o1 o2 den hNv hmv ho1v ho2v hdv
  have hdenpos : 0 < sampleDenominator num := Nat.pow_pos hu
  have hceil : sampleArgument N m (o1 * o2) num den ≤
      sampleNumerator N m (o1 * o2) den + sampleDenominator num := by
    unfold sampleArgument
    rw [ceil_div_nat _ _ hdenpos]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hlog : Nat.clog 2 (sampleArgument N m (o1 * o2) num den) ≤
      sampleArgument N m (o1 * o2) num den := clog_le_self _
  have henc := sampleExponent_encoding N m (o1 * o2) num den eta hun hdd hu hd
  unfold sampleExponentProgram
  refine Hx.hs (Hs.then (assign_spec rationalNumReg (by decide) (by decide)
    sampleNumeratorExpression a
    (by simp (config := { decide := true }) [sampleNumeratorExpression, powerExpression, AE.vars_ok])
    (by decide) hc
    (positiveProduct_ok a.env _ C.Wd hpos (by rw [heval]; omega)))
    (fun b ⟨hbn, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbn' : b.env rationalNumReg = sampleNumerator N m (o1 * o2) den := hbn.trans heval
  have hbu : b.env etaNumReg = num := (hbfr _ (by decide) (by decide) (by decide)).trans huv
  have hdeneval : sampleDenominatorExpression.eval b.env = sampleDenominator num := by
    simp only [sampleDenominatorExpression, powerExpression_eval, AE.eval, hbu, sampleDenominator]
  have hdenpositive : PositiveProduct b.env sampleDenominatorExpression :=
    powerExpression_positive b.env (.var etaNumReg) 8 (by change 0 < b.env etaNumReg; rw [hbu]; exact hu)
  refine Hs.then (assign_spec rationalDenReg (by decide) (by decide)
    sampleDenominatorExpression b
    (by simp (config := { decide := true }) [sampleDenominatorExpression, powerExpression, AE.vars_ok])
    (by decide) hbc
    (positiveProduct_ok b.env _ C.Wd hdenpositive (by rw [hdeneval]; omega)))
    (fun d ⟨hdden, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hdden' : d.env rationalDenReg = sampleDenominator num := hdden.trans hdeneval
  have hdnum : d.env rationalNumReg = sampleNumerator N m (o1 * o2) den :=
    (hdfr _ (by decide) (by decide) (by decide)).trans hbn'
  refine Hs.then (rationalCeilProgram_spec C d hdc _ _ hdnum hdden' hdenpos (by omega))
    (fun e ⟨hearg, hecp, hewq, heout, hec, hefr⟩ n3 hn3 => ?_)
  have hearg' : e.env rationalCeilReg = sampleArgument N m (o1 * o2) num den := hearg
  refine Hs.last (clogSixteenProgram_spec C e hec _ hearg' (by omega))
    (fun f ⟨hfq, hfcp, hfwq, hfout, hfc, hffr⟩ n4 hn4 => ?_)
  refine ⟨⟨?_, hfcp.trans (hecp.trans (hdcp.trans hbcp)),
    hfwq.trans (hewq.trans (hdwq.trans hbwq)),
    hfout.trans (heout.trans (hdout.trans hbout)), hfc, ?_⟩, ?_⟩
  · rw [henc]
    exact hfq
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (FrS.weaken hefr (by decide)) (FrS.weaken hffr (by decide))))
  · simp only [sampleNumeratorExpression, sampleDenominatorExpression, powerExpression, AE.cost] at hn1 hn2
    omega

end NearQuarticWires.StagePrep
