import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# Public bounds for the exact integer printer

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The physical atom count of `sec:params`, paper/paper.tex. -/
def printingAtomCount (n m : ℕ) : ℕ := (4 * m + 1) * (2 * n ^ 4)

/-- The exact child count of `sec:params`, paper/paper.tex. -/
def printingChildCount (n B lam : ℕ) : ℕ := n * (B + lam + 3)

/-- The occurrence envelope of `sec:params`, paper/paper.tex. -/
def printingOccurrenceCount (n m B lam : ℕ) : ℕ :=
  1 + printingAtomCount n m * printingChildCount n B lam

/-- The integer bound computation of `sec:params`,
paper/paper.tex, preserves binary encodings. -/
def printingSizesProgram : St VV :=
  .seq (.op (.copy t3 vN)) (.seq (powK 4)
    (.seq (assign atomsReg (mul (add (mul (lit 4) (var mReg)) (lit 1)) (mul (lit 2) (var t5))))
      (.seq (assign childCapReg (mul (var vN) (add (add (var vB0) (var pLAM)) (lit 3))))
        (assign occurrenceCapReg (add (lit 1) (mul (var atomsReg) (var childCapReg)))))))

/-- The public printer bounds of `sec:params`, paper/paper.tex, are computed exactly in a constant number of
fixed-width arithmetic instructions. -/
theorem printingSizesProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n m B lam : ℕ) (hnv : a.env vN = n) (hmv : a.env mReg = m)
    (hBv : a.env vB0 = B) (hlv : a.env pLAM = lam) (hn : 0 < n)
    (hW : printingAtomCount n m * printingChildCount n B lam +
      printingAtomCount n m + printingChildCount n B lam +
      2 * n ^ 4 + (4 * m + 1) + (B + lam + 3) + 128 < 2 ^ C.Wd) :
    Hs C printingSizesProgram a 150 (fun b =>
      b.env atomsReg = printingAtomCount n m ∧
      b.env childCapReg = printingChildCount n B lam ∧
      b.env occurrenceCapReg = printingOccurrenceCount n m B lam ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [t3, t5, t6, atomsReg, childCapReg, occurrenceCapReg, vJ]) := by
  have hn4 : n ^ 4 < 2 ^ C.Wd := by omega
  have hpow : ∀ j ≤ 4, n ^ j < 2 ^ C.Wd := by
    intro j hj
    exact (Nat.pow_le_pow_right hn hj).trans_lt hn4
  have hatom : (4 * m + 1) * (2 * n ^ 4) < 2 ^ C.Wd := by
    change printingAtomCount n m < _
    omega
  have hchild : n * (B + lam + 3) < 2 ^ C.Wd := by
    change printingChildCount n B lam < _
    omega
  unfold printingSizesProgram
  refine Hx.hs (Hs.then (hs_copy C t3 vN a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set t3 (a.env vN)) := hc.set _ _ (by decide)
  refine Hs.then (powK_spec _ hc0 4 (by
    intro j hj; rw [DS.set_env_self, hnv]; exact hpow j hj))
    (fun b ⟨hbn4, _, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_)
  have hbn4' : b.env t5 = n ^ 4 := by simpa only [DS.set_env_self, hnv] using hbn4
  have hbm : b.env mReg = m := by rw [hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hmv]
  refine Hs.then (assign_spec atomsReg (by decide) (by decide)
    (.mul (.add (.mul (.lit 4) (.var mReg)) (.lit 1)) (.mul (.lit 2) (.var t5))) b
    (by aevar) (by aevar) hbc (by aeok [hbm, hbn4']))
    (fun d ⟨hda, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hda' : d.env atomsReg = printingAtomCount n m := by
    simpa only [AE.eval, hbm, hbn4', printingAtomCount] using hda
  have hdn : d.env vN = n := by
    rw [hdfr _ (by decide) (by decide) (by decide), hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hnv]
  have hdB : d.env vB0 = B := by
    rw [hdfr _ (by decide) (by decide) (by decide), hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hBv]
  have hdl : d.env pLAM = lam := by
    rw [hdfr _ (by decide) (by decide) (by decide), hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hlv]
  refine Hs.then (assign_spec childCapReg (by decide) (by decide)
    (.mul (.var vN) (.add (.add (.var vB0) (.var pLAM)) (.lit 3))) d
    (by aevar) (by aevar) hdc (by aeok [hdn, hdB, hdl]))
    (fun e ⟨hec, hefr, hecp, hewq, heout, heconst⟩ n3 hn3 => ?_)
  have hec' : e.env childCapReg = printingChildCount n B lam := by
    simpa only [AE.eval, hdn, hdB, hdl, printingChildCount] using hec
  have hea : e.env atomsReg = printingAtomCount n m :=
    (hefr _ (by decide) (by decide) (by decide)).trans hda'
  refine Hs.last (assign_spec occurrenceCapReg (by decide) (by decide)
    (.add (.lit 1) (.mul (.var atomsReg) (.var childCapReg))) e
    (by aevar) (by aevar) heconst (by aeok [hea, hec', printingOccurrenceCount]))
    (fun f ⟨hfo, hffr, hfcp, hfwq, hfout, hfc⟩ n4 hn4 => ?_)
  refine ⟨⟨?_, ?_, ?_, hfcp.trans (hecp.trans (hdcp.trans hbcp)),
    hfwq.trans (hewq.trans (hdwq.trans hbwq)),
    hfout.trans (heout.trans (hdout.trans hbout)), hfc, ?_⟩, ?_⟩
  · rw [hffr _ (by decide) (by decide) (by decide), hea]
  · rw [hffr _ (by decide) (by decide) (by decide), hec']
  · simpa only [AE.eval, hea, hec', printingOccurrenceCount] using hfo
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (FrS.weaken hbfr.toS (by decide))
        (FrS.trans (hdfr.toS _ (by decide) (by decide))
          (FrS.trans (hefr.toS _ (by decide) (by decide)) (hffr.toS _ (by decide) (by decide)))))
  · simp only [AE.cost] at hn2 hn3 hn4
    omega

end NearQuarticWires.StagePrep
