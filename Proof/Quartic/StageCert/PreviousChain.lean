import Proof.Quartic.StageCert.ChainSource
import Proof.Quartic.StageCert.LinearCoefficient

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testE` and `lem:print`, paper/paper.tex: the original digit row is saved while its predecessor is read. -/
def savedChainRow : Fin VV := ⟨119,by decide⟩

/-- `eq:testE` and `lem:print`, paper/paper.tex: row zero has zero subtrahend; every later row reads its
actual predecessor and then restores the requested row. -/
def readPreviousChain (store : Fin MM) : St VV MM :=
  .ite (.eq chainRow vZ) (.op (.zero linearNegative))
    (.seq (.op (.copy savedChainRow chainRow))
      (.seq (.op (.sub chainRow v1))
        (.seq (readChainRecord store linearNegative) (.op (.copy chainRow savedChainRow)))))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the predecessor coefficient is obtained
by an actual retained-source read, with the zero row and all source
bytes handled exactly before any column certification. -/
theorem readPreviousChain_run (C : Ctx) (store : Fin MM)
    (G row J k g : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G) (hr : a.env chainRow=row)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd) :
    Hs C (readPreviousChain store) a (a.rc store+5*bits.length+40) (fun z=>
      z.env linearNegative=(if row=0 then 0 else
        if row-1<J then (bits.getD (row*G+k+g) false).toNat else 0) ∧
      z.env chainRow=row ∧
      StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      z.rc store≤bits.length ∧ Cst z ∧
      Fr a z [savedChainRow,chainRow,linearNegative,sourceRecordLimit,atomValue,
        sourceRecordIndex,sourceRecordDiscard]) := by
  unfold readPreviousChain
  refine Hs.ite (t := a.rc store+5*bits.length+39) (c := .eq chainRow vZ)
    (show chainRow≠vZ by decide) ?_ ?_
  · intro he
    have hzero : row=0 := by simpa only [Cnd.eval,hr,hc.z,decide_eq_true_eq] using he
    refine (hs_zero C linearNegative a).mono (by omega) ?_
    rintro z rfl
    exact ⟨by simp [hzero],by rw [DS.set_env_ne _ _ (by decide)]; exact hr,rfl,hcursor,
      Cst.of_fr (T := [linearNegative]) hc (Fr.set _ _ (by simp)) (by decide),
      Fr.set _ _ (by simp)⟩
  · intro he
    have hne : row≠0 := by simpa only [Cnd.eval,hr,hc.z,decide_eq_false_iff_not] using he
    have hpos : 0<row := by omega
    apply Hx.hs
    refine Hs.then (hs_copy C savedChainRow chainRow a (by decide))
      (fun b hb' n1 hn1=>?_)
    subst hb'
    let b := a.set savedChainRow (a.env chainRow)
    refine Hs.then (hs_sub C chainRow v1 b (by decide) (by
      change a.env v1≤a.env chainRow
      rw [hr,hc.one]
      omega))
      (fun d hd n2 hn2=>?_)
    subst hd
    let d := b.set chainRow (b.env chainRow-b.env v1)
    have df : Fr a d [savedChainRow,chainRow] :=
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))
    have dc : Cst d := Cst.of_fr hc df (by decide)
    have dr : d.env chainRow=row-1 := by
      change a.env chainRow-a.env v1=row-1
      rw [hr,hc.one]
    refine Hs.then (readChainRecord_source C store linearNegative (by decide)
      G (row-1) J k g bits d dc hG hgG
      ((df _ (by decide)).trans hb) dr ((df _ (by decide)).trans hJ)
      ((df _ (by decide)).trans hk) ((df _ (by decide)).trans hg)
      hram hcursor hbits hbound)
      (fun q ⟨qn,qs,qr,qc,qfr⟩ n3 hn3=>?_)
    have qsave : q.env savedChainRow=row := by
      rw [qfr _ (by decide)]
      change a.env chainRow=row
      exact hr
    refine Hs.last (hs_copy C chainRow savedChainRow q (by decide))
      (fun z hz n4 hn4=>?_)
    subst hz
    refine ⟨⟨?_,by simp only [DS.set_env_self,qsave],qs,qr,?_,?_⟩,?_⟩
    · rw [DS.set_env_ne _ _ (by decide),if_neg hne,qn]
      rw [show row-1+1=row by omega]
    · exact Cst.of_fr (T := [chainRow]) qc (Fr.set _ _ (by simp)) (by decide)
    · exact (df.weaken (by decide)).trans ((qfr.weaken (by decide)).trans (Fr.set _ _ (by simp)))
    · change n3≤a.rc store+5*bits.length+30 at hn3
      omega

end NearQuarticWires.StageCert.Tokens
