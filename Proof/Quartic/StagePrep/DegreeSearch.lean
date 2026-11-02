import Proof.Quartic.StagePrep.DegreeTest

/-!
# The finite greatest-degree computation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The finite degree search of `sec:params`, paper/paper.tex, starts at the original arity and counts down. -/
def degreeSearchProgram : St VV :=
  .seq (.op (.copy pSI vN))
    (.seq (fgScan pSI pSF degreeTestProgram) (.op (.copy pDM pSI)))

/-- The search in `sec:params`, paper/paper.tex, computes the literal `findGreatest` result in a
linear number of constant-cost integer predicate evaluations. -/
theorem degreeSearchProgram_spec (C : Ctx) (a : DS VV) (hc : Cst a)
    (n m k ell : ℕ) (hn : a.env vN = n) (hm : a.env mReg = m)
    (hk : a.env pK = k) (hl : a.env degreeLogReg = ell)
    (hW : 100 * (m * k + 2 + n * ell) + n + k + 256 < 2 ^ C.Wd) :
    Hs C degreeSearchProgram a (400 * (n + 2)) (fun b =>
      b.env pDM = Nat.findGreatest (fun D => 100 * (m * k + 2 + D * ell) ≤ n - k) n ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b [pSI, pSF, pX5, pX6, pDM, vJ]) := by
  let T : List (Fin VV) := [pSI, pSF, pX5, pX6, pDM, vJ]
  let I : DS VV → Prop := fun b =>
    b.env vN = n ∧ b.env mReg = m ∧ b.env pK = k ∧ b.env degreeLogReg = ell ∧
    Cst b ∧ FrS a b T
  have hset : ∀ (x : Fin VV), vN ≠ x → mReg ≠ x → pK ≠ x → degreeLogReg ≠ x →
      x ∉ [vZ, v1, v2, vPOS] → x ∈ T → ∀ b v, I b → I (b.set x v) := by
    intro x hxN hxM hxK hxL hxSafe hxT b v hb
    obtain ⟨hbn, hbm, hbk, hbl, hbc, hbfr⟩ := hb
    exact ⟨by rw [DS.set_env_ne _ _ hxN]; exact hbn,
      by rw [DS.set_env_ne _ _ hxM]; exact hbm,
      by rw [DS.set_env_ne _ _ hxK]; exact hbk,
      by rw [DS.set_env_ne _ _ hxL]; exact hbl,
      hbc.set _ _ hxSafe, FrS.trans hbfr (Fr.toS (Fr.set _ _ hxT))⟩
  have htest : FlagTest C degreeTestProgram pSI pSF
      (fun D => 100 * (m * k + 2 + D * ell) ≤ n - k) I 300 n := by
    intro b hb hv
    obtain ⟨hbn, hbm, hbk, hbl, hbc, hbfr⟩ := hb
    refine Hs.mono (degreeTestProgram_spec C b hbc n m k ell (b.env pSI)
      hbn hbm hbk hbl rfl hv hW) le_rfl ?_
    rintro d ⟨hdf, hdv, hdcp, hdwq, hdout, hdc, hdfr⟩
    refine ⟨hdf, hdv, ?_, hdcp, hdwq, hdout⟩
    exact ⟨(hdfr _ (by decide) (by decide)).trans hbn,
      (hdfr _ (by decide) (by decide)).trans hbm,
      (hdfr _ (by decide) (by decide)).trans hbk,
      (hdfr _ (by decide) (by decide)).trans hbl,
      hdc, FrS.trans hbfr (FrS.weaken hdfr (by decide))⟩
  unfold degreeSearchProgram
  refine Hx.hs (Hs.then (hs_copy C pSI vN a (by decide))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have hI : I (a.set pSI (a.env vN)) :=
    ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hn,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hm,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hk,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hl,
      hc.set _ _ (by decide), Fr.toS (Fr.set _ _ (by decide))⟩
  refine Hs.then (fgScan_spec pSI pSF (by decide) (by decide) (by decide) (by decide)
    degreeTestProgram (fun D => 100 * (m * k + 2 + D * ell) ≤ n - k) I 300
    (fun b hb => hb.2.2.2.2.1)
    (hset pSF (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hset pSI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    n htest _ hI (by rw [DS.set_env_self, hn]))
    (fun b ⟨hbd, hbI, hbcp, hbwq, hbout⟩ n1 hn1 => ?_)
  obtain ⟨_, _, _, _, hbc, hbfr⟩ := hbI
  refine Hs.last (hs_copy C pDM pSI b (by decide)) ?_
  rintro d rfl n2 hn2
  exact ⟨⟨by rw [DS.set_env_self, hbd], hbcp, hbwq, hbout,
    hbc.set _ _ (by decide), FrS.trans hbfr (Fr.toS (Fr.set _ _ (by decide)))⟩, by omega⟩

end NearQuarticWires.StagePrep
