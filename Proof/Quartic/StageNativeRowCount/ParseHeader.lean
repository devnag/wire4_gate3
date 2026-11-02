import Proof.Quartic.StageNativeRowCount.ReadScalar

set_option autoImplicit false

namespace NearQuarticWires.StageNativeRowCount

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the retained
header parser reads n/r/b, skips the two width codecs, and never
numerically decodes the remaining syndrome/translation fields. -/
def parseHeader (rd : Fin VV → Op VV MM) : St VV MM :=
  .seq (readScalar rd nReg) (.seq (skipNatural rd)
    (.seq (skipNatural rd) (.seq (readScalar rd rReg) (readScalar rd bReg))))

def parseHeaderCost (n Lin Lout r b : ℕ) : ℕ :=
  30*(natBitLength n+natBitLength r+natBitLength b)+
    20*(natBitLength Lin+natBitLength Lout)+200

/-- `lem:print` and `prop:time`, paper/paper.tex: all decoding/skipping follows actual bytes and leaves
the trailing translation payload entirely uninterpreted. -/
theorem parseHeader_spec {C : Ctx} {R : Type} (S : Src C R)
    (a : DS VV MM) (hc : Cst a) (hok : S.ok a)
    (n Lin Lout r b : ℕ) (rest : List Bool)
    (hin : S.word.drop (S.pos a) =
      [n,Lin,Lout,r,b].flatMap natWord ++ rest)
    (hW : ∀ v ∈ [n,Lin,Lout,r,b], natBitLength v+2 ≤ C.Wd) :
    Hs C (parseHeader S.op) a (parseHeaderCost n Lin Lout r b) (fun d =>
      d.env nReg=n ∧ d.env rReg=r ∧ d.env bReg=b ∧
      S.rest d=S.rest a ∧ Cst d) := by
  have hi : S.word.drop (S.pos a) = natWord n ++
      ([Lin,Lout,r,b].flatMap natWord ++ rest) := by simpa only [List.flatMap_cons,List.append_assoc] using hin
  unfold parseHeader
  refine Hx.hs (Hs.then (readScalar_spec S nReg (by decide) (by decide) a hc hok n _ hi
    (hW n (by simp))) ?_)
  rintro d ⟨dn,dp,dr,dc,dfr⟩ k0 hk0
  have di := source_tail S dp hi
  have dok : S.ok d := S.ok_of _ _ dr hok
  have di' : S.word.drop (S.pos d) = natWord Lin ++
      ([Lout,r,b].flatMap natWord ++ rest) := by simpa only [List.flatMap_cons,List.append_assoc] using di
  refine Hs.then (skipNatural_spec S d dc dok Lin _ di' (hW Lin (by simp))) ?_
  rintro e ⟨ep,er,efr⟩ k1 hk1
  have ec := cst_fr dc efr
  have ei := source_tail S ep di'
  have en : e.env nReg=n := by rw [efr nReg (by decide),dn]
  have eok : S.ok e := S.ok_of _ _ (er.trans dr) hok
  have ei' : S.word.drop (S.pos e) = natWord Lout ++
      ([r,b].flatMap natWord ++ rest) := by simpa only [List.flatMap_cons,List.append_assoc] using ei
  refine Hs.then (skipNatural_spec S e ec eok Lout _ ei' (hW Lout (by simp))) ?_
  rintro f ⟨fp,fr,ffr⟩ k2 hk2
  have fc := cst_fr ec ffr
  have fi := source_tail S fp ei'
  have fn : f.env nReg=n := by rw [ffr nReg (by decide),en]
  have fok : S.ok f := S.ok_of _ _ (fr.trans (er.trans dr)) hok
  have fi' : S.word.drop (S.pos f) = natWord r ++
      ([b].flatMap natWord ++ rest) := by simpa only [List.flatMap_cons,List.append_assoc] using fi
  refine Hs.then (readScalar_spec S rReg (by decide) (by decide) f fc fok r _ fi'
    (hW r (by simp))) ?_
  rintro g ⟨gr,gp,gs,gc,gfr⟩ k3 hk3
  have gi := source_tail S gp fi'
  have gn : g.env nReg=n := by rw [gfr nReg (by decide),fn]
  have gok : S.ok g := S.ok_of _ _ (gs.trans (fr.trans (er.trans dr))) hok
  have gi' : S.word.drop (S.pos g) = natWord b ++ rest := by simpa using gi
  refine Hs.last (readScalar_spec S bReg (by decide) (by decide) g gc gok b rest gi'
    (hW b (by simp))) ?_
  rintro q ⟨qb,_,qs,qc,qfr⟩ k4 hk4
  refine ⟨⟨by rw [qfr nReg (by decide),gn],by rw [qfr rReg (by decide),gr],qb,
    qs.trans (gs.trans (fr.trans (er.trans dr))),qc⟩,?_⟩
  unfold parseHeaderCost
  omega

end NearQuarticWires.StageNativeRowCount
