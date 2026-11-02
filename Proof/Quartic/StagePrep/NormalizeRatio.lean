import Proof.Quartic.StagePrep.RationalCeil

/-!
# Canonical rational fields for the parameter word

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`. Rational fields are
reduced before their literal `ratWord` is emitted.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The exact reduction of a nonnegative rational field in
`sec:params`, paper/paper.tex. -/
def normalizeRatioProgram : St VV :=
  .seq (.op (.copy GCA rationalNumReg))
    (.seq (.op (.copy GCB rationalDenReg)) (.seq gcdv
      (.seq (assign rationalNumReg (div (var rationalNumReg) (var GCA)))
        (assign rationalDenReg (div (var rationalDenReg) (var GCA))))))

/-- The rational-field reduction of `sec:params`,
paper/paper.tex, computes the exact canonical
numerator and denominator, with a bit-size cost bound. -/
theorem normalizeRatioProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (A B : ℕ) (hA : a.env rationalNumReg = A)
    (hB : a.env rationalDenReg = B) (hBpos : 0 < B)
    (hW : 2 * (A + B) + 4 < 2 ^ C.Wd) :
    Hs C normalizeRatioProgram a (14 * (Nat.size A + Nat.size B) + 40) (fun b =>
      b.env rationalNumReg = ((A : ℚ) / B).num.natAbs ∧
      b.env rationalDenReg = ((A : ℚ) / B).den ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [rationalNumReg, rationalDenReg, GCA, GCB, GCQ, GCR, vJ]) := by
  have hgpos : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_right _ hBpos
  have hgle : Nat.gcd A B ≤ B := Nat.gcd_le_right _ hBpos
  unfold normalizeRatioProgram
  refine Hx.hs (Hs.then (hs_copy C GCA rationalNumReg a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_copy C GCB rationalDenReg _ (by decide))
    (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  let b := (a.set GCA (a.env rationalNumReg)).set GCB
    ((a.set GCA (a.env rationalNumReg)).env rationalDenReg)
  have hbc : Cst b := (hc.set GCA _ (by decide)).set GCB _ (by decide)
  have hbx : b.env GCA = A := by
    simp only [b]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hA]
  have hby : b.env GCB = B := by
    simp only [b]
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hB]
  refine Hs.then (gcdv_spec b hbc A B (A + B) hbx hby (by omega) (by omega) (by omega))
    (fun d ⟨hdg, hdcp, hdwq, hdout, hdc, hdfr⟩ n2 hn2 => ?_)
  have hdA : d.env rationalNumReg = A := by
    rw [hdfr _ (by decide)]
    simp only [b]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hA]
  have hdB : d.env rationalDenReg = B := by
    rw [hdfr _ (by decide)]
    simp only [b]
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hB]
  refine Hs.then (assign_spec rationalNumReg (by decide) (by decide)
    (.div (.var rationalNumReg) (.var GCA)) d (by aevar) (by aevar) hdc
    (by aeok [hdA, hdg]))
    (fun e ⟨hen, hefr, hecp, hewq, heout, hec⟩ n3 hn3 => ?_)
  have heB : e.env rationalDenReg = B :=
    (hefr _ (by decide) (by decide) (by decide)).trans hdB
  have heg : e.env GCA = Nat.gcd A B :=
    (hefr _ (by decide) (by decide) (by decide)).trans hdg
  refine Hs.last (assign_spec rationalDenReg (by decide) (by decide)
    (.div (.var rationalDenReg) (.var GCA)) e (by aevar) (by aevar) hec
    (by aeok [heB, heg]))
    (fun f ⟨hfd, hffr, hfcp, hfwq, hfout, hfc⟩ n4 hn4 => ?_)
  obtain ⟨hqn, hqd⟩ := rat_div_reduce A B hBpos
  refine ⟨⟨?_, ?_, hfcp.trans (hecp.trans hdcp),
    hfwq.trans (hewq.trans hdwq), hfout.trans (heout.trans hdout), hfc, ?_⟩, ?_⟩
  · rw [hffr _ (by decide) (by decide) (by decide), hen, hqn]
    simp only [AE.eval, hdA, hdg, Int.natAbs_natCast]
  · simpa only [AE.eval, heB, heg, hqd] using hfd
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
        (FrS.trans (FrS.weaken hdfr.toS (by decide))
          (FrS.trans (hefr.toS _ (by decide) (by decide)) (hffr.toS _ (by decide) (by decide)))))
  · simp only [AE.cost] at hn3 hn4
    omega

end NearQuarticWires.StagePrep
