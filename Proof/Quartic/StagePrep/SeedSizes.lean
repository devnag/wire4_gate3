import Proof.Quartic.StagePrep.ParameterRegisters
import Proof.Quartic.StagePrep.MaxRegister

/-!
# The sample size, field width, and seed length

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The binary sample-size and seed-length rules of
`sec:params`, paper/paper.tex. -/
def seedSizesProgram : St VV :=
  .seq (.op (.copy P2E qExponentReg)) (.seq pow2v
    (.seq (.op (.copy qReg P2X))
      (.seq (assign pX1 (add (var qExponentReg) (lit 1)))
        (.seq (maxRegister ellFieldReg pK pX1)
          (assign seedLengthReg (mul (mul (lit 2) (var mReg)) (var ellFieldReg)))))))

/-- The rules of `sec:params`, paper/paper.tex, construct `Q` by binary shifts and store the exact
field width and seed length. -/
theorem seedSizesProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (e k m : ℕ) (he : a.env qExponentReg = e) (hk : a.env pK = k)
    (hm : a.env mReg = m) (heW : e < C.Wd)
    (hW : 2 * m * max k (e + 1) + k + e + 32 < 2 ^ C.Wd) :
    Hs C seedSizesProgram a (5 * e + 80) (fun b =>
      b.env qReg = 2 ^ e ∧ b.env ellFieldReg = max k (e + 1) ∧
      b.env seedLengthReg = 2 * m * max k (e + 1) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [P2E, P2X, P2I, qReg, pX1, ellFieldReg, seedLengthReg, vJ]) := by
  have hmax : 0 < max k (e + 1) := by omega
  have hmBound : 2 * m ≤ 2 * m * max k (e + 1) := Nat.le_mul_of_pos_right _ hmax
  unfold seedSizesProgram
  refine Hx.hs (Hs.then (hs_copy C P2E qExponentReg a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set P2E (a.env qExponentReg)) := hc.set _ _ (by decide)
  refine Hs.then (pow2v_spec _ hc0 e (by rw [DS.set_env_self, he]) heW)
    (fun b ⟨hbx, hbcp, hbwq, hbout, hbc, hbfr⟩ n1 hn1 => ?_)
  refine Hs.then (hs_copy C qReg P2X b (by decide)) (fun d hd n2 hn2 => ?_)
  subst hd
  have hdc : Cst (b.set qReg (b.env P2X)) := hbc.set _ _ (by decide)
  have hde : (b.set qReg (b.env P2X)).env qExponentReg = e := by
    rw [DS.set_env_ne _ _ (by decide), hbfr _ (by decide), DS.set_env_ne _ _ (by decide), he]
  refine Hs.then (assign_spec pX1 (by decide) (by decide)
    (.add (.var qExponentReg) (.lit 1)) _ (by aevar) (by aevar) hdc (by aeok [hde]))
    (fun f ⟨hfx, hffr, hfcp, hfwq, hfout, hfc⟩ n3 hn3 => ?_)
  have hfx' : f.env pX1 = e + 1 := by simpa only [AE.eval, hde] using hfx
  have hfk : f.env pK = k := by
    rw [hffr _ (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide),
      hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hk]
  have hfm : f.env mReg = m := by
    rw [hffr _ (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide),
      hbfr _ (by decide), DS.set_env_ne _ _ (by decide), hm]
  refine Hs.then (maxRegister_spec C ellFieldReg pK pX1 (by decide) (by decide)
    (by decide) (by decide) f hfc)
    (fun g ⟨hgl, hgcp, hgwq, hgout, hgc, hgfr⟩ n4 hn4 => ?_)
  have hgl' : g.env ellFieldReg = max k (e + 1) := by simpa only [hfk, hfx'] using hgl
  have hgm : g.env mReg = m := (hgfr _ (by decide)).trans hfm
  refine Hs.last (assign_spec seedLengthReg (by decide) (by decide)
    (.mul (.mul (.lit 2) (.var mReg)) (.var ellFieldReg)) g
    (by aevar) (by aevar) hgc (by aeok [hgm, hgl']))
    (fun h ⟨hhs, hhfr, hhcp, hhwq, hhout, hhc⟩ n5 hn5 => ?_)
  refine ⟨⟨?_, ?_, ?_, hhcp.trans (hgcp.trans (hfcp.trans hbcp)),
    hhwq.trans (hgwq.trans (hfwq.trans hbwq)),
    hhout.trans (hgout.trans (hfout.trans hbout)), hhc, ?_⟩, ?_⟩
  · rw [hhfr _ (by decide) (by decide) (by decide), hgfr _ (by decide),
      hffr _ (by decide) (by decide) (by decide), DS.set_env_self, hbx]
  · rw [hhfr _ (by decide) (by decide) (by decide), hgl']
  · simpa only [AE.eval, hgm, hgl'] using hhs
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (FrS.weaken hbfr.toS (by decide))
        (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
          (FrS.trans (hffr.toS _ (by decide) (by decide))
            (FrS.trans (FrS.weaken hgfr.toS (by decide)) (hhfr.toS _ (by decide) (by decide))))))
  · simp only [AE.cost] at hn3 hn5
    omega

end NearQuarticWires.StagePrep
