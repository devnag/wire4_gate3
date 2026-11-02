import Proof.Quartic.StagePrep.NormalizeRatio

/-!
# The canonical rational sampling precision

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open AE

/-- The original rational radius in `sec:params`,
paper/paper.tex, gives an exact integer ratio
for the sampling precision. -/
theorem eta_ratio_encoding (beta : ℚ) (num den MF : ℕ)
    (hnum : beta.num = num) (hden : beta.den = den)
    (hd : 0 < den) (hMF : 0 < MF) :
    beta / (16 * MF : ℕ) = (num : ℚ) / (16 * MF * den : ℕ) := by
  have hb : beta = (num : ℚ) / den := by
    have h := Rat.num_div_den beta
    rw [hnum, hden] at h
    simpa only [Int.cast_natCast] using h.symm
  have hd0 : (den : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hMF0 : (MF : ℚ) ≠ 0 := by exact_mod_cast hMF.ne'
  rw [hb]
  push_cast
  field_simp

/-- The reduced sampling precision of `sec:params`,
paper/paper.tex. -/
def etaProgram : St VV :=
  .seq (.op (.copy rationalNumReg vNUM))
    (.seq (assign rationalDenReg (mul (mul (lit 16) (var mFourierReg)) (var vDEN)))
      (.seq normalizeRatioProgram (.seq (.op (.copy etaNumReg rationalNumReg))
        (.op (.copy etaDenReg rationalDenReg)))))

/-- The precision computation of `sec:params`, paper/paper.tex, writes the exact canonical rational fields. -/
theorem etaProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (num den MF : ℕ) (beta : ℚ)
    (hnumv : a.env vNUM = num) (hdenv : a.env vDEN = den)
    (hMFv : a.env mFourierReg = MF)
    (hbn : beta.num = num) (hbd : beta.den = den)
    (hd : 0 < den) (hMF : 0 < MF)
    (hW : 2 * (num + 16 * MF * den) + 4 < 2 ^ C.Wd) :
    Hs C etaProgram a (14 * (Nat.size num + Nat.size (16 * MF * den)) + 120) (fun b =>
      b.env etaNumReg = (beta / (16 * MF : ℕ)).num.natAbs ∧
      b.env etaDenReg = (beta / (16 * MF : ℕ)).den ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [rationalNumReg, rationalDenReg, GCA, GCB, GCQ, GCR,
        etaNumReg, etaDenReg, vJ]) := by
  have h16MF : 16 * MF ≤ 16 * MF * den := Nat.le_mul_of_pos_right _ hd
  have h16 : 16 ≤ 16 * MF := Nat.le_mul_of_pos_right _ hMF
  have hBpos : 0 < 16 * MF * den := Nat.mul_pos (Nat.mul_pos (by norm_num) hMF) hd
  have heta := eta_ratio_encoding beta num den MF hbn hbd hd hMF
  unfold etaProgram
  refine Hx.hs (Hs.then (hs_copy C rationalNumReg vNUM a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hc0 : Cst (a.set rationalNumReg (a.env vNUM)) := hc.set _ _ (by decide)
  have hbMF : (a.set rationalNumReg (a.env vNUM)).env mFourierReg = MF := by
    rw [DS.set_env_ne _ _ (by decide), hMFv]
  have hbDen : (a.set rationalNumReg (a.env vNUM)).env vDEN = den := by
    rw [DS.set_env_ne _ _ (by decide), hdenv]
  refine Hs.then (assign_spec rationalDenReg (by decide) (by decide)
    (.mul (.mul (.lit 16) (.var mFourierReg)) (.var vDEN)) _
    (by aevar) (by aevar) hc0 (by aeok [hbMF, hbDen]))
    (fun d ⟨hdd, hdfr, hdcp, hdwq, hdout, hdc⟩ n1 hn1 => ?_)
  have hdd' : d.env rationalDenReg = 16 * MF * den := by
    simpa only [AE.eval, hbMF, hbDen] using hdd
  have hdn : d.env rationalNumReg = num := by
    rw [hdfr _ (by decide) (by decide) (by decide), DS.set_env_self, hnumv]
  refine Hs.then (normalizeRatioProgram_spec C d hdc num (16 * MF * den) hdn hdd' hBpos hW)
    (fun e ⟨hen, hed, hecp, hewq, heout, hec, hefr⟩ n2 hn2 => ?_)
  refine Hs.then (hs_copy C etaNumReg rationalNumReg e (by decide)) (fun f hf n3 hn3 => ?_)
  subst hf
  refine Hs.last (hs_copy C etaDenReg rationalDenReg _ (by decide)) ?_
  rintro g rfl n4 hn4
  refine ⟨⟨?_, ?_, hecp.trans hdcp, hewq.trans hdwq, heout.trans hdout,
    (hec.set etaNumReg _ (by decide)).set etaDenReg _ (by decide), ?_⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hen, heta]
  · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hed, heta]
  · exact FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
      (FrS.trans (hdfr.toS _ (by decide) (by decide))
        (FrS.trans (FrS.weaken hefr (by decide))
          (FrS.trans (Fr.toS (Fr.set _ _ (by decide)))
            (Fr.toS (Fr.set _ _ (by decide))))))
  · simp only [AE.cost] at hn1
    omega

end NearQuarticWires.StagePrep
