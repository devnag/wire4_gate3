import Proof.Quartic.StageCert.ChainFrame

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- (W3), `sec:walks` and `lem:print`, paper/paper.tex: an actual chain-bit read retains the
complete source remainder, including every other store cursor and the
already emitted formula tokens. -/
theorem readChainRecord_source (C : Ctx) (store : Fin MM) (target : Fin VV)
    (htarget : target≠vZ ∧ target≠v1 ∧ target≠v2)
    (G row J k g : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G) (hr : a.env chainRow=row)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd) :
    Hs C (readChainRecord store target) a (a.rc store+5*bits.length+30) (fun z=>
      z.env target=(if row<J then (bits.getD ((row+1)*G+k+g) false).toNat else 0) ∧
      StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      z.rc store≤bits.length ∧ Cst z ∧
      Fr a z [target,sourceRecordLimit,atomValue,sourceRecordIndex,sourceRecordDiscard]) := by
  obtain ⟨z,n,he,hn,zt,zs,zr,zc,zfr⟩ := readChainRecord_run C store target htarget
    G row J k g bits a hc hG hgG hb hr hJ hk hg hram hcursor hbits hbound
  refine ⟨z,n,he,hn,zt,?_,zr,zc,zfr⟩
  have zo : z.out=a.out := readChainRecord_output store target he
  have zrc : Function.update z.rc store 0=Function.update a.rc store 0 := by
    funext other
    by_cases ho : other=store
    · simp [ho]
    · simpa [Function.update_of_ne ho] using
        (readChainRecord_otherStore store other ho target he).2
  simp only [StageLift.memorySourceRest,Prod.mk.injEq] at zs ⊢
  exact ⟨zs.1,zo,zs.2.1,zrc,zs.2.2.1,zs.2.2.2.1,zs.2.2.2.2⟩

end NearQuarticWires.StageCert.Tokens
