import Proof.Quartic.StagePrep.DegreeLog
import Proof.Gates.Dispatch.ParamsB

/-!
# The exact bounded printing-degree test

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- One degree comparison in `sec:params`, paper/paper.tex, uses the cached exact logarithm. -/
def degreeTestProgram : St VV :=
  .seq (assign pX6 (mul (lit 100)
    (add (add (mul (var mReg) (var pK)) (lit 2)) (mul (var pSI) (var degreeLogReg)))))
    (.seq (assign pX5 (sub (var vN) (var pK))) (flagLe pSF pX6 pX5))

/-- The degree predicate in `sec:params`, paper/paper.tex, is computed exactly with a uniform finite
instruction count for every candidate at most the arity. -/
theorem degreeTestProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n m k ell v : ℕ) (hn : a.env vN = n) (hm : a.env mReg = m)
    (hk : a.env pK = k) (hl : a.env degreeLogReg = ell) (hv : a.env pSI = v)
    (hvn : v ≤ n)
    (hW : 100 * (m * k + 2 + n * ell) + n + k + 256 < 2 ^ C.Wd) :
    Hs C degreeTestProgram a 300 (fun b =>
      b.env pSF = bnat (100 * (m * k + 2 + v * ell) ≤ n - k) ∧
      b.env pSI = v ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [pSF, pX5, pX6, vJ]) := by
  have hvl : v * ell ≤ n * ell := Nat.mul_le_mul_right _ hvn
  have hinner : m * k + 2 + n * ell ≤ 100 * (m * k + 2 + n * ell) :=
    Nat.le_mul_of_pos_left _ (by norm_num)
  have hsmall : 100 * (m * k + 2 + v * ell) < 2 ^ C.Wd := by
    have hp := Nat.mul_le_mul_left 100 (Nat.add_le_add_left hvl (m * k + 2))
    omega
  unfold degreeTestProgram
  refine Hx.hs (Hs.then (assign_spec pX6 (by decide) (by decide)
    (.mul (.lit 100) (.add (.add (.mul (.var mReg) (.var pK)) (.lit 2))
      (.mul (.var pSI) (.var degreeLogReg)))) a
    (by aevar) (by aevar) hc (by aeok [hm, hk, hv, hl]))
    (fun b ⟨hbx, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbx' : b.env pX6 = 100 * (m * k + 2 + v * ell) := by
    simpa only [AE.eval, hm, hk, hv, hl] using hbx
  have hbn : b.env vN = n := (hbfr _ (by decide) (by decide) (by decide)).trans hn
  have hbk : b.env pK = k := (hbfr _ (by decide) (by decide) (by decide)).trans hk
  refine Hs.then (assign_spec pX5 (by decide) (by decide)
    (.sub (.var vN) (.var pK)) b (by aevar) (by aevar) hbc (by exact ⟨trivial, trivial⟩))
    (fun d ⟨hdy, hdfr, hdcp, hdwq, hdout, hdc⟩ n2 hn2 => ?_)
  have hdy' : d.env pX5 = n - k := by simpa only [AE.eval, hbn, hbk] using hdy
  have hdx : d.env pX6 = 100 * (m * k + 2 + v * ell) :=
    (hdfr _ (by decide) (by decide) (by decide)).trans hbx'
  refine Hs.last (flagLe_spec pSF pX6 pX5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) d hdc (by omega))
    (fun e ⟨hef, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  have hfr : FrS a e [pSF, pX5, pX6, vJ] :=
    FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (hdfr.toS _ (by decide) (by decide)) (hefr.toS _ (by decide) (by decide)))
  refine ⟨⟨?_, ?_, hecp.trans (hdcp.trans hbcp), hewq.trans (hdwq.trans hbwq),
    heout.trans (hdout.trans hbout), hec, hfr⟩, ?_⟩
  · rw [hef, hdx, hdy']
  · exact (hfr _ (by decide) (by decide)).trans hv
  · simp only [AE.cost] at hn1 hn2
    omega

end NearQuarticWires.StagePrep
