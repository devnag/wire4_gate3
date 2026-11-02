import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.CeilSqrt

/-!
# Integer Fourier widths and their square-root envelope

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The full frequency-count product of `sec:params`,
paper/paper.tex. -/
def fourierTheta (m G1 G2 : ℕ) : ℕ := (4 * m * G1 + 1) * (4 * m * G2 + 1)

/-- The exact integer widths and `MF` of `sec:params`,
paper/paper.tex. -/
def fourierSizesProgram : St VV :=
  .seq (assign omegaOneReg (add (mul (mul (lit 4) (var mReg)) (var vG1)) (lit 1)))
    (.seq (assign omegaTwoReg (add (mul (mul (lit 4) (var mReg)) (var vG2)) (lit 1)))
      (.seq (assign SQX (mul (var omegaOneReg) (var omegaTwoReg)))
        (.seq ceilSqrtProgram (.op (.copy mFourierReg SQS)))))

/-- The program for `sec:params`, paper/paper.tex, retains both exact widths and computes their canonical
natural square-root envelope, including an empty circuit. -/
theorem fourierSizesProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (m G1 G2 : ℕ) (hm : a.env mReg = m)
    (hG1 : a.env vG1 = G1) (hG2 : a.env vG2 = G2)
    (hW : fourierTheta m G1 G2 * fourierTheta m G1 G2 +
      fourierTheta m G1 G2 + 4 * m + 16 < 2 ^ C.Wd) :
    Hs C fourierSizesProgram a (20 * fourierTheta m G1 G2 + 160) (fun b =>
      b.env omegaOneReg = 4 * m * G1 + 1 ∧
      b.env omegaTwoReg = 4 * m * G2 + 1 ∧
      b.env mFourierReg = Cells.ParameterArithmetic.ceilSqrt (fourierTheta m G1 G2) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [omegaOneReg, omegaTwoReg, SQX, SQS, SQF, SQT, SQU, mFourierReg, vJ]) := by
  have htheta : fourierTheta m G1 G2 < 2 ^ C.Wd := by omega
  have hOne : 4 * m * G1 + 1 ≤ fourierTheta m G1 G2 := Nat.le_mul_of_pos_right _ (by omega)
  have hTwo : 4 * m * G2 + 1 ≤ fourierTheta m G1 G2 := Nat.le_mul_of_pos_left _ (by omega)
  unfold fourierSizesProgram
  refine Hx.hs (Hs.then (assign_spec omegaOneReg (by decide) (by decide)
    (.add (.mul (.mul (.lit 4) (.var mReg)) (.var vG1)) (.lit 1)) a
    (by aevar) (by aevar) hc (by aeok [hm, hG1]))
    (fun b ⟨hbo, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbo' : b.env omegaOneReg = 4 * m * G1 + 1 := by simpa only [AE.eval, hm, hG1] using hbo
  have hbm : b.env mReg = m := (hbfr _ (by decide) (by decide) (by decide)).trans hm
  have hbG2 : b.env vG2 = G2 := (hbfr _ (by decide) (by decide) (by decide)).trans hG2
  refine Hs.then (assign_spec omegaTwoReg (by decide) (by decide)
    (.add (.mul (.mul (.lit 4) (.var mReg)) (.var vG2)) (.lit 1)) b
    (by aevar) (by aevar) hbc (by aeok [hbm, hbG2]))
    (fun d ⟨hdo, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hdo' : d.env omegaTwoReg = 4 * m * G2 + 1 := by simpa only [AE.eval, hbm, hbG2] using hdo
  have hdOne : d.env omegaOneReg = 4 * m * G1 + 1 :=
    (hdfr _ (by decide) (by decide) (by decide)).trans hbo'
  refine Hs.then (assign_spec SQX (by decide) (by decide)
    (.mul (.var omegaOneReg) (.var omegaTwoReg)) d (by aevar) (by aevar) hdc
    (by aeok [hdOne, hdo', fourierTheta]))
    (fun e ⟨hex, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  have hex' : e.env SQX = fourierTheta m G1 G2 := by
    simpa only [AE.eval, hdOne, hdo', fourierTheta] using hex
  refine Hs.then (ceilSqrtProgram_spec C e hec _ hex' (by omega))
    (fun f ⟨hfrt, hfcp, hfwq, hfout, hfc, hffr⟩ n4 hn4 => ?_)
  refine Hs.last (hs_copy C mFourierReg SQS f (by decide)) ?_
  rintro g rfl n5 hn5
  refine ⟨⟨?_, ?_, ?_, hfcp.trans (hecp.trans (hdcp.trans hbcp)),
    hfwq.trans (hewq.trans (hdwq.trans hbwq)), hfout.trans (heout.trans (hdout.trans hbout)),
    hfc.set _ _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), hffr _ (by decide),
      hefr _ (by decide) (by decide) (by decide), hdOne]
  · rw [DS.set_env_ne _ _ (by decide), hffr _ (by decide),
      hefr _ (by decide) (by decide) (by decide), hdo']
  · rw [DS.set_env_self, hfrt]
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (hefr.toS _ (by decide) (by decide))
          (FrS.trans (FrS.weaken hffr.toS (by decide)) (Fr.toS (Fr.set _ _ (by decide))))))
  · simp only [AE.cost] at hn1 hn2 hn3
    omega

end NearQuarticWires.StagePrep
