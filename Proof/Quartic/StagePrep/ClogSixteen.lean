import Proof.Quartic.StagePrep.RationalCeil

/-!
# The base-sixteen ceiling logarithm

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The base-sixteen logarithm of `sec:params`,
paper/paper.tex, is a rounded binary logarithm. -/
theorem clog_sixteen (x : ℕ) : Nat.clog 16 x = (Nat.clog 2 x + 3) / 4 := by
  exact Nat.clog_pow_left 2 4 x

/-- The sample-exponent logarithm of `sec:params`,
paper/paper.tex, uses binary halving and division. -/
def clogSixteenProgram : St VV :=
  .seq (.op (.copy t3 rationalCeilReg))
    (.seq clog2 (assign qExponentReg (div (add (var t5) (lit 3)) (lit 4))))

/-- The logarithm program of `sec:params`, paper/paper.tex, computes the exact natural base-sixteen clog. -/
theorem clogSixteenProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (x : ℕ) (hx : a.env rationalCeilReg = x)
    (hW : 2 * x + Nat.clog 2 x + 10 < 2 ^ C.Wd) :
    Hs C clogSixteenProgram a (5 * Nat.clog 2 x + 50) (fun b =>
      b.env qExponentReg = Nat.clog 16 x ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [t3, t5, t6, qExponentReg, vJ]) := by
  unfold clogSixteenProgram
  refine Hx.hs (Hs.then (hs_copy C t3 rationalCeilReg a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hbc : Cst (a.set t3 (a.env rationalCeilReg)) := hc.set _ _ (by decide)
  have hbt3 : (a.set t3 (a.env rationalCeilReg)).env t3 = x := by rw [DS.set_env_self, hx]
  refine Hs.then (clog2_spec _ hbc (by rw [hbt3]; omega))
    (fun d ⟨hdl, _, hdcp, hdwq, hdout, hdc, hdfr⟩ n1 hn1 => ?_)
  have hdl' : d.env t5 = Nat.clog 2 x := by simpa only [hbt3] using hdl
  refine Hs.last (assign_spec qExponentReg (by decide) (by decide)
    (.div (.add (.var t5) (.lit 3)) (.lit 4)) d
    (by aevar) (by aevar) hdc (by aeok [hdl']))
    (fun e ⟨heq, hefr, hecp, hewq, heout, hec⟩ n2 hn2 => ?_)
  refine ⟨⟨?_, hecp.trans hdcp, hewq.trans hdwq, heout.trans hdout, hec, ?_⟩, ?_⟩
  · rw [clog_sixteen]
    simpa only [AE.eval, hdl'] using heq
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (FrS.weaken hdfr.toS (by decide)) (hefr.toS _ (by decide) (by decide)))
  · simp only [AE.cost] at hn2
    have hn1' : n1 ≤ 5 * Nat.clog 2 x + 6 := by simpa only [hbt3] using hn1
    omega

end NearQuarticWires.StagePrep
