import Proof.Quartic.StageCert.MaskProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- (W3) and `lem:print`, paper/paper.tex: the actual proposed-chain row is binary metadata during
linear coefficient generation, after the walk masks have been emitted. -/
def chainRow : Fin VV := ⟨124,by decide⟩
/-- (W3) and `lem:print`, paper/paper.tex: the actual number of retained chain rows. -/
def chainRows : Fin VV := ⟨125,by decide⟩

/-- (W3) and `lem:print`, paper/paper.tex: compute the original concatenated occurrence's exact retained
chain-bit address `(row+1)G+k+g`. -/
def prepareChainAddress : St VV MM :=
  .seq (.op (.copy sourceRecordLimit chainRow))
    (.seq (.op (.inc sourceRecordLimit))
      (.seq (.op (.mul sourceRecordLimit atomCount atomValue))
        (.seq (.op (.copy sourceRecordLimit atomValue))
          (.seq (.op (.add sourceRecordLimit selectionStart))
            (.op (.add sourceRecordLimit atomOccurrence))))))

/-- (W3) and `lem:print`, paper/paper.tex: chain indices are actual bounded binary arithmetic, with
the original row, occurrence, bank size and source stores retained. -/
theorem prepareChainAddress_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (G row k g : ℕ) (hG : 1≤G) (hb : a.env atomCount=G) (hr : a.env chainRow=row)
    (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hfit : (row+1)*G+k+g<2^C.Wd) :
    Hs C prepareChainAddress a 11 (fun z=>
      z.env sourceRecordLimit=(row+1)*G+k+g ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [sourceRecordLimit,atomValue]) := by
  have hrow : row+1<2^C.Wd := by nlinarith
  unfold prepareChainAddress
  refine Hs.seq (t1 := 1) (t2 := 9)
    (hs_copy C sourceRecordLimit chainRow a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 7)
    (hs_inc C sourceRecordLimit _ (by vsimp [hr]; exact hrow)) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := 5)
    (hs_mul C sourceRecordLimit atomCount atomValue _ (by decide) (by decide) (by decide)
      (by vsimp [hr,hb]; omega)) ?_
  rintro e rfl
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_copy C sourceRecordLimit atomValue _ (by decide)) ?_
  rintro f rfl
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_add C sourceRecordLimit selectionStart _ (by decide) (by vsimp [hr,hb,hk]; omega)) ?_
  rintro q rfl
  refine (hs_add C sourceRecordLimit atomOccurrence _ (by decide)
    (by vsimp [hr,hb,hk,hg]; exact hfit)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by vsimp [hr,hb,hk,hg],rfl,
    ⟨by vsimp [hc.z],by vsimp [hc.one],by vsimp [hc.two]⟩,
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))))⟩

end NearQuarticWires.StageCert.Tokens
