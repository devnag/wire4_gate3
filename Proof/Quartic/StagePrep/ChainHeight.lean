import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Gates.Dispatch.ParamsE

/-!
# The exact chain height and initial scale

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The height and initial scale in `sec:params`,
paper/paper.tex, are integer operations. -/
def chainHeightProgram : St VV :=
  .seq (assign pHE (div (var pP) (lit 4)))
    (.seq (assign pH (div (var pHE) (mul (lit 2) (var mReg))))
      (assign ellZeroReg (mul (mul (lit 32) (var mReg)) (var pU))))

/-- The height computation of `sec:params`, paper/paper.tex, implements the new height rule and retains the
integer initial scale without square-root substitution. -/
theorem chainHeightProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (P m U : ℕ) (hPv : a.env pP = P) (hmv : a.env mReg = m)
    (hUv : a.env pU = U) (hm : 0 < m) (hU : 0 < U)
    (hW : 32 * m * U + 4 < 2 ^ C.Wd) :
    Hs C chainHeightProgram a 150 (fun b =>
      b.env pHE = P / 4 ∧ b.env pH = P / 4 / (2 * m) ∧
      b.env ellZeroReg = 32 * m * U ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ FrS a b [pHE, pH, ellZeroReg, vJ]) := by
  have h32m : 32 * m ≤ 32 * m * U := Nat.le_mul_of_pos_right _ hU
  have h2m : 2 * m ≤ 32 * m := Nat.mul_le_mul_right _ (by omega)
  unfold chainHeightProgram
  refine Hx.hs (Hs.then (assign_spec pHE (by decide) (by decide)
    (.div (.var pP) (.lit 4)) a (by aevar) (by aevar) hc (by aeok []))
    (fun b ⟨hb, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hb' : b.env pHE = P / 4 := by simpa only [AE.eval, hPv] using hb
  have hbm : b.env mReg = m := (hbfr _ (by decide) (by decide) (by decide)).trans hmv
  refine Hs.then (assign_spec pH (by decide) (by decide)
    (.div (.var pHE) (.mul (.lit 2) (.var mReg))) b
    (by aevar) (by aevar) hbc (by aeok [hbm]))
    (fun d ⟨hd, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hd' : d.env pH = P / 4 / (2 * m) := by
    simpa only [AE.eval, hb', hbm] using hd
  have hdm : d.env mReg = m := (hdfr _ (by decide) (by decide) (by decide)).trans hbm
  have hdU : d.env pU = U := by
    rw [hdfr _ (by decide) (by decide) (by decide),
      hbfr _ (by decide) (by decide) (by decide), hUv]
  refine Hs.last (assign_spec ellZeroReg (by decide) (by decide)
    (.mul (.mul (.lit 32) (.var mReg)) (.var pU)) d
    (by aevar) (by aevar) hdc (by aeok [hdm, hdU])) ?_
  rintro e ⟨he, hefr, hecp, hewq, heout, hec⟩ n3 hn3
  refine ⟨⟨?_, ?_, ?_, hecp.trans (hdcp.trans hbcp),
    hewq.trans (hdwq.trans hbwq), heout.trans (hdout.trans hbout), hec,
    FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (hefr.toS _ (by decide) (by decide)))⟩, ?_⟩
  · rw [hefr _ (by decide) (by decide) (by decide),
      hdfr _ (by decide) (by decide) (by decide), hb']
  · rw [hefr _ (by decide) (by decide) (by decide), hd']
  · simpa only [AE.eval, hdm, hdU] using he
  · simp only [AE.cost] at hn1 hn2 hn3
    omega

end NearQuarticWires.StagePrep
