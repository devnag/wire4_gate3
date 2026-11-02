import Proof.Quartic.StageHamming.DataStep

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def dataPositionScratch : List (Fin VV) := dataIndex :: dataStepScratch

/-- `imp:partition`, paper/paper.tex: the bounded
coordinate scan constructs the requested canonical data position. -/
def dataPositionLoop : St VV MM := forS dataIndex dataLimit dataPositionStep

/-- `imp:partition` and `prop:time`, paper/paper.tex: the real bounded scan produces the exact filtered-list
lookup while retaining its original input parameters. -/
theorem dataPositionLoop_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (b s m : ℕ) (hb : a.env dataLimit = b) (hswidth : a.env parityWidth = s)
    (hm : a.env dataTarget = m) (hcount : a.env dataCount = 0)
    (hanswer : a.env dataAnswer = 0)
    (hbW : b < 2 ^ C.Wd) (hs : s < 2 ^ C.Wd) (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C dataPositionLoop a (b * (8 * s + 24) + 4) (fun d =>
      d.env dataCount = (dataPrefix s b).length ∧
      d.env dataAnswer = (dataPrefix s b).getD m 0 ∧
      d.sh = a.sh ∧ Fr a d dataPositionScratch) := by
  let Inv : ℕ → DS VV MM → Prop := fun k d =>
    d.env dataCount = (dataPrefix s k).length ∧
    d.env dataAnswer = (dataPrefix s k).getD m 0 ∧
    d.env dataTarget = m ∧ d.env parityWidth = s ∧ d.sh = a.sh ∧
    Fr a d dataPositionScratch
  have hloop := forS_spec' (C := C) dataIndex dataLimit (by decide)
    dataPositionStep a b hbW Inv (8 * s + 20)
    (fun k d v hd => by
      obtain ⟨hdcount, hdanswer, hdtarget, hdwidth, hdsh, hdfr⟩ := hd
      exact ⟨(DS.set_env_ne _ _ (by decide)).trans hdcount,
        (DS.set_env_ne _ _ (by decide)).trans hdanswer,
        (DS.set_env_ne _ _ (by decide)).trans hdtarget,
        (DS.set_env_ne _ _ (by decide)).trans hdwidth,
        hdsh, hdfr.trans (Fr.set _ _ (by simp [dataPositionScratch]))⟩)
    (by exact ⟨by simpa [dataPrefix] using hcount,
      by simpa [dataPrefix] using hanswer, hm, hswidth, rfl, Fr.refl _ _⟩)
    hb ?_
  · refine hloop.mono (by apply le_of_eq; ring) ?_
    rintro d ⟨⟨hdcount, hdanswer, _, _, hdsh, hdfr⟩, _, _⟩
    exact ⟨hdcount, hdanswer, hdsh, hdfr⟩
  · intro k hk d hd hindex hlimit
    obtain ⟨hdcount, hdanswer, hdtarget, hdwidth, hdsh, hdfr⟩ := hd
    have hcd : Cst d := hc.of_fr hdfr (by decide)
    refine (dataPositionStep_spec d hcd k s m hindex hdwidth hdtarget hdcount hdanswer
      (by omega) hs hW).mono le_rfl ?_
    rintro e ⟨hecount, heanswer, hesh, hefr⟩
    refine ⟨⟨hecount, heanswer, (hefr _ (by decide)).trans hdtarget,
      (hefr _ (by decide)).trans hdwidth, hesh.trans hdsh,
      hdfr.trans (hefr.weaken (by decide))⟩,
      (hefr _ (by decide)).trans hindex, (hefr _ (by decide)).trans hlimit⟩

/-- `imp:partition`, paper/paper.tex: both lookup
accumulators are initialized by the actual data-position program. -/
def dataPosition : St VV MM :=
  .seq (.op (.zero dataCount)) (.seq (.op (.zero dataAnswer)) dataPositionLoop)

/-- `imp:partition` and `prop:time`, paper/paper.tex: exact canonical data-position lookup is computed from
the scalar width and index with its complete polynomial scan cost. -/
theorem dataPosition_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (b s m : ℕ) (hb : a.env dataLimit = b) (hswidth : a.env parityWidth = s)
    (hm : a.env dataTarget = m)
    (hbW : b < 2 ^ C.Wd) (hs : s < 2 ^ C.Wd) (hW : 2 ^ s < 2 ^ C.Wd) :
    Hs C dataPosition a (b * (8 * s + 24) + 8) (fun d =>
      d.env dataCount = (dataPrefix s b).length ∧
      d.env dataAnswer = (dataPrefix s b).getD m 0 ∧
      d.sh = a.sh ∧ Fr a d dataPositionScratch) := by
  unfold dataPosition
  refine Hx.hs (Hs.then (hs_zero C dataCount a) (fun b hb' n1 hn1 => ?_))
  subst hb'
  let a1 := a.set dataCount 0
  refine Hs.then (hs_zero C dataAnswer a1) (fun d hd n2 hn2 => ?_)
  subst hd
  let a2 := a1.set dataAnswer 0
  have hf : Fr a a2 dataPositionScratch :=
    (Fr.set a _ (by simp [dataPositionScratch, dataStepScratch])).trans
      (Fr.set a1 _ (by simp [dataPositionScratch, dataStepScratch]))
  have hca2 : Cst a2 := hc.of_fr hf (by decide)
  refine Hs.last (dataPositionLoop_spec a2 hca2 b s m
    ((hf _ (by decide)).trans hb) ((hf _ (by decide)).trans hswidth)
    ((hf _ (by decide)).trans hm)
    (by vsimp [a2, a1]) (by rw [DS.set_env_self]) hbW hs hW) ?_
  rintro e ⟨hecount, heanswer, hesh, hefr⟩ n3 hn3
  exact ⟨⟨hecount, heanswer, hesh, hf.trans hefr⟩, by omega⟩

/-- `imp:partition`, paper/paper.tex: the completed
physical lookup returns the same `dpos` used by the canonical encoder. -/
theorem dataPosition_dpos_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (m : ℕ) (hb : a.env dataLimit = P.b)
    (hswidth : a.env parityWidth = P.s) (hm : a.env dataTarget = m)
    (hbW : P.b < 2 ^ C.Wd) (hs : P.s < 2 ^ C.Wd) (hW : 2 ^ P.s < 2 ^ C.Wd) :
    Hs C dataPosition a (P.b * (8 * P.s + 24) + 8) (fun d =>
      d.env dataAnswer = PrimT.C4Geo.dpos P m ∧
      d.sh = a.sh ∧ Fr a d dataPositionScratch) :=
  (dataPosition_spec a hc P.b P.s m hb hswidth hm hbW hs hW).mono le_rfl
    (fun _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)

end NearQuarticWires.StageHamming
