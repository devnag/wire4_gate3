import Proof.Quartic.StagePrep.NormalizeRatio
import Proof.Gates.Dispatch.ParamsB

/-!
# The canonical rational masking density

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The reduced rational `pi0` of `sec:params`, paper/paper.tex. -/
def piProgram : St VV :=
  .seq (.op (.copy rationalNumReg tauReg))
    (.seq (assign rationalDenReg (mul (lit 4) (var pU)))
      (.seq normalizeRatioProgram (.seq (.op (.copy piNumReg rationalNumReg))
        (.op (.copy piDenReg rationalDenReg)))))

/-- The masking density of `sec:params`, paper/paper.tex, is computed in canonical rational encoding. -/
theorem piProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (tau U : ℕ) (ht : a.env tauReg = tau) (hU : a.env pU = U) (hUpos : 0 < U)
    (hW : 2 * (tau + 4 * U) + 4 < 2 ^ C.Wd) :
    Hs C piProgram a (14 * (Nat.size tau + Nat.size (4 * U)) + 100) (fun b =>
      b.env piNumReg = ((tau : ℚ) / (4 * U : ℕ)).num.natAbs ∧
      b.env piDenReg = ((tau : ℚ) / (4 * U : ℕ)).den ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [rationalNumReg, rationalDenReg, GCA, GCB, GCQ, GCR,
        piNumReg, piDenReg, vJ]) := by
  unfold piProgram
  refine Hx.hs (Hs.then (hs_copy C rationalNumReg tauReg a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set rationalNumReg (a.env tauReg)) := hc.set _ _ (by decide)
  have hbU : (a.set rationalNumReg (a.env tauReg)).env pU = U := by
    rw [DS.set_env_ne _ _ (by decide), hU]
  refine Hs.then (assign_spec rationalDenReg (by decide) (by decide)
    (.mul (.lit 4) (.var pU)) _ (by aevar) (by aevar) hc0 (by aeok [hbU]))
    (fun d ⟨hdd, hdfr, hdcp, hdwq, hdout, hdc⟩ n1 hn1 => ?_)
  have hdd' : d.env rationalDenReg = 4 * U := by simpa only [AE.eval, hbU] using hdd
  have hdn : d.env rationalNumReg = tau := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_self, ht]
  refine Hs.then (normalizeRatioProgram_spec C d hdc tau (4 * U) hdn hdd'
    (by omega) hW)
    (fun e ⟨hen, hed, hecp, hewq, heout, hec, hefr⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C piNumReg rationalNumReg e (by decide)) (fun f hf n3 hn3 => ?_)
  subst hf
  refine Hs.last (hs_copy C piDenReg rationalDenReg _ (by decide)) ?_
  rintro g rfl n4 hn4
  refine ⟨⟨?_, ?_, hecp.trans hdcp, hewq.trans hdwq, heout.trans hdout,
    (hec.set piNumReg _ (by decide)).set piDenReg _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hen]
  · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hed]
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (FrS.weaken hefr (by decide))
          (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
            (Fr.toS (Fr.set _ _ (by decide))))))
  · simp only [AE.cost] at hn1
    omega

end NearQuarticWires.StagePrep
