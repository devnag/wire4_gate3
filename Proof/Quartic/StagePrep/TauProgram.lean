import Proof.Quartic.StagePrep.RationalCeil
import Proof.Quartic.StagePrep.TauArithmetic

/-!
# Physical computation of the masking threshold

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The masking-threshold computation in `sec:params`,
paper/paper.tex, uses the original rational radius. -/
def tauProgram : St VV :=
  .seq (assign rationalNumReg (mul (lit 16) (var vDEN)))
    (.seq (.op (.copy rationalDenReg vNUM))
      (.seq rationalCeilProgram (.seq (.op (.copy t3 rationalCeilReg))
        (.seq clog2 (assign tauReg (add (var pK) (var t5)))))))

/-- The masking-threshold work of `sec:params`,
paper/paper.tex, depends on the binary logarithm. -/
def tauCost (beta : ℚ) : ℕ :=
  5 * Cells.ParameterArithmetic.ceilLog 2 (16 / beta) + 100

/-- The physical computation of `sec:params`, paper/paper.tex, writes the exact canonical masking threshold. -/
theorem tauProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (k num den : ℕ) (beta : ℚ) (hk : a.env pK = k)
    (hnum : a.env vNUM = num) (hden : a.env vDEN = den)
    (hbn : beta.num = num) (hbd : beta.den = den) (hnumpos : 0 < num)
    (hW : k + 32 * den + 4 * num + 16 < 2 ^ C.Wd) :
    Hs C tauProgram a (tauCost beta) (fun b =>
      b.env tauReg = k + Cells.ParameterArithmetic.ceilLog 2 (16 / beta) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [rationalNumReg, rationalDenReg, rationalCeilReg, t3, t5, t6, tauReg, vJ]) := by
  let z : ℕ := ⌈((16 * den : ℕ) : ℚ) / num⌉₊
  have hz : z ≤ 16 * den + num := tau_ceil_bound num den hnumpos
  have hclog : Nat.clog 2 z ≤ z := clog_le_self z
  have hlog : Cells.ParameterArithmetic.ceilLog 2 (16 / beta) = Nat.clog 2 z :=
    tau_log_encoding beta num den hbn hbd
  unfold tauProgram
  refine Hx.hs (Hs.then (assign_spec rationalNumReg (by decide) (by decide)
    (.mul (.lit 16) (.var vDEN)) a (by aevar) (by aevar) hc (by aeok [hden]))
    (fun b ⟨hbnumer, hbfr, hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbnumer' : b.env rationalNumReg = 16 * den := by simpa only [AE.eval, hden] using hbnumer
  have hbnum : b.env vNUM = num := (hbfr _ (by decide) (by decide) (by decide)).trans hnum
  refine Hs.then (hs_copy C rationalDenReg vNUM b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  have hdc : Cst (b.set rationalDenReg (b.env vNUM)) := hbc.set _ _ (by decide)
  refine Hs.then (rationalCeilProgram_spec C _ hdc (16 * den) num
    (by rw [DS.set_env_ne _ _ (by decide), hbnumer'])
    (by rw [DS.set_env_self, hbnum]) hnumpos (by omega))
    (fun e ⟨hec, hecp, hewq, heout, heconst, hefr⟩ n3 hn3 => ?_)
  have hec' : e.env rationalCeilReg = z := hec
  refine Hs.then (hs_copy C t3 rationalCeilReg e (by decide)) (fun f hf n4 hn4 => ?_)
  subst hf
  have hfc : Cst (e.set t3 (e.env rationalCeilReg)) := heconst.set _ _ (by decide)
  have hft3 : (e.set t3 (e.env rationalCeilReg)).env t3 = z := by rw [DS.set_env_self, hec']
  refine Hs.then (clog2_spec _ hfc (by rw [hft3]; omega))
    (fun g ⟨hgl, _, hgcp, hgwq, hgout, hgc, hgfr⟩ n5 hn5 => ?_)
  have hgl' : g.env t5 = Nat.clog 2 z := by simpa only [hft3] using hgl
  have hgk : g.env pK = k := by
    rw [hgfr _ (by decide), DS.set_env_ne _ _ (by decide),
      hefr _ (by decide) (by decide), DS.set_env_ne _ _ (by decide),
      hbfr _ (by decide) (by decide) (by decide), hk]
  refine Hs.last (assign_spec tauReg (by decide) (by decide)
    (.add (.var pK) (.var t5)) g (by aevar) (by aevar) hgc (by aeok [hgk, hgl']))
    (fun h ⟨hht, hhfr, hhcp, hhwq, hhout, hhc⟩ n6 hn6 => ?_)
  refine ⟨⟨?_, hhcp.trans (hgcp.trans (hecp.trans hbcp)),
    hhwq.trans (hgwq.trans (hewq.trans hbwq)),
    hhout.trans (hgout.trans (heout.trans hbout)), hhc, ?_⟩, ?_⟩
  · simpa only [AE.eval, hgk, hgl', hlog] using hht
  · exact FrS.trans (hbfr.toS _ (by decide) (by decide))
      (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
        (FrS.trans (FrS.weaken hefr (by decide))
          (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
            (FrS.trans (FrS.weaken hgfr.toS (by decide)) (hhfr.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hn1 hn6
    have hn5' : n5 ≤ 5 * Nat.clog 2 z + 6 := by simpa only [hft3] using hn5
    unfold tauCost
    rw [hlog]
    omega

end NearQuarticWires.StagePrep
