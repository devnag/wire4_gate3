import Proof.Quartic.StageCert.ChainAddress

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- (W3), `sec:walks` and `lem:print`, paper/paper.tex: read an original chain bit only inside
its actual retained row range; absent rows have the original zero value. -/
def readChainRecord (store : Fin MM) (target : Fin VV) : St VV MM :=
  .ite (.lt chainRow chainRows)
    (.seq prepareChainAddress (readSourceRecord store target)) (.op (.zero target))

/-- (W3), `sec:walks` and `lem:print`, paper/paper.tex: the complete proposed-chain bit comes from
its actual retained witness records. The out-of-range zero branch reads
no nonexistent source record and retains every original source byte. -/
theorem readChainRecord_run (C : Ctx) (store : Fin MM) (target : Fin VV)
    (htarget : target≠vZ ∧ target≠v1 ∧ target≠v2)
    (G row J k g : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G) (hr : a.env chainRow=row)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd) :
    Hs C (readChainRecord store target) a (a.rc store+5*bits.length+30) (fun z=>
      z.env target=(if row<J then (bits.getD ((row+1)*G+k+g) false).toNat else 0) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧
      Fr a z [target,sourceRecordLimit,atomValue,sourceRecordIndex,sourceRecordDiscard]) := by
  unfold readChainRecord
  refine Hs.ite (t := a.rc store+5*bits.length+29) (c := .lt chainRow chainRows)
    (show chainRow≠chainRows by decide) ?_ ?_
  · intro he
    have hrow : row<J := by simpa only [Cnd.eval,hr,hJ,decide_eq_true_eq] using he
    have hindex : (row+1)*G+k+g<bits.length := by nlinarith
    have hfit : (row+1)*G+k+g<2^C.Wd := by nlinarith
    refine (Hs.seq (t1 := 11) (t2 := a.rc store+5*((row+1)*G+k+g)+8)
      (prepareChainAddress_run C a hc G row k g hG hb hr hk hg hfit) ?_).mono (by omega) (fun _ h=>h)
    rintro b ⟨bi,bs,bc,bfr⟩
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
    have brc : b.rc=a.rc := congrArg (fun q=>q.2.2.2.1) bs
    refine (readSourceRecord_run C store target htarget b bc ((row+1)*G+k+g) bi
      (by rw [bram,hram,List.length_map]; exact hindex) hfit).mono (by rw [brc]) ?_
    rintro z ⟨zt,zr,zs,zc,zfr⟩
    have zsmall : (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) := by
      simp only [StageLift.memorySourceRest,DS.sh,Prod.mk.injEq] at zs bs
      simp only [Prod.mk.injEq]
      exact ⟨zs.1.trans bs.1,zs.2.2.1.trans bs.2.2.1,
        zs.2.2.2.2.1.trans bs.2.2.2.2.1,zs.2.2.2.2.2.1.trans bs.2.2.2.2.2.1,
        zs.2.2.2.2.2.2.trans bs.2.2.2.2.2.2⟩
    refine ⟨?_,zsmall,by omega,zc,
      (bfr.weaken (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        tauto)).trans (zfr.weaken (by
        intro x hx
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
        tauto))⟩
    rw [if_pos hrow,zt,bram,hram,List.getD_eq_getElem _ _ (by simpa using hindex),List.getElem_map]
    simp only [List.getD_eq_getElem _ _ hindex]
  · intro he
    have hrow : ¬row<J := by simpa only [Cnd.eval,hr,hJ,decide_eq_false_iff_not] using he
    refine (hs_zero C target a).mono (by omega) ?_
    rintro z rfl
    exact ⟨by simp [hrow],rfl,hcursor,
      Cst.of_fr (T := [target]) hc (Fr.set _ _ (by simp))
        (by simpa only [List.mem_singleton] using ⟨Ne.symm htarget.1,Ne.symm htarget.2.1,Ne.symm htarget.2.2⟩),
      Fr.set _ _ (by simp)⟩

end NearQuarticWires.StageCert.Tokens
