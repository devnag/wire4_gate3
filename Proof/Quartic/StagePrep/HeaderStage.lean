import Proof.Quartic.StagePrep.CanonicalProgram

/-!
# The first guarded parameter stage

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates

/-- The first stage of `sec:params`, paper/paper.tex, computes its literal fields and exact initial guard.
Both outcomes have the same finite public work bound. -/
theorem preparationHeaderStage_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n w1 w2 : ℕ) (hn : a.env vN = n)
    (hw1 : a.env vTW1 = w1) (hw2 : a.env vTW2 = w2)
    (ha : a.env vADM = 1)
    (hW : (3 * n + 4) * (n + 1) + w1 + w2 + 100 * n + 100 < 2 ^ C.Wd) :
    Hs C preparationHeaderStage a (20 * n + 250) (fun b =>
      b.env pLAM = Target.lambda n ∧ b.env pMU = Target.mu n ∧
      b.env pJM = Target.mu n + 1 ∧ b.env mReg = 4 ∧
      b.env rReg = 16 * Target.mu n ∧ b.env pW = a.env censusTotal ∧
      b.env vADM = bnat (4 * (16 * Target.mu n) ≤ n) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b (parameterHeaderT ++ [pX1, vADM, vJ])) := by
  have hmu : Target.mu n ≤ n := (clog_le_self _).trans (clog_le_self n)
  unfold preparationHeaderStage
  refine Hx.hs (Hs.then (parameterHeader_spec C a hc n w1 w2 hn hw1 hw2 (by omega))
    (fun b ⟨hbl, hbm, hbJ, hbm4, hbr, hbW, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_))
  have hbA : b.env vADM = bnat True := by
    rw [hbfr _ (by decide) (by decide), ha]
    decide
  have hbn : b.env vN = n := (hbfr _ (by decide) (by decide)).trans hn
  refine Hs.last (checkedLe_spec C b hbc pX1 vN (.mul (.lit 4) (.var rReg)) True hbA
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by aevar) (by aevar) (by aeok [hbr])) ?_
  rintro d ⟨hdA, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hdcp.trans hbcp,
    hdwq.trans hbwq, hdout.trans hbout, hdc,
    FrS.trans (FrS.weaken hbfr (by decide)) (FrS.weaken hdfr (by decide))⟩, ?_⟩
  · exact (hdfr _ (by decide) (by decide)).trans hbl
  · exact (hdfr _ (by decide) (by decide)).trans hbm
  · exact (hdfr _ (by decide) (by decide)).trans hbJ
  · exact (hdfr _ (by decide) (by decide)).trans hbm4
  · exact (hdfr _ (by decide) (by decide)).trans hbr
  · exact (hdfr _ (by decide) (by decide)).trans hbW
  · simpa only [AE.eval, hbr, hbn, true_and] using hdA
  · simp only [AE.cost] at hn2
    omega

end NearQuarticWires.StagePrep
