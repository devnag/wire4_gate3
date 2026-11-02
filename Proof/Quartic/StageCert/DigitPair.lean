import Proof.Quartic.StageCert.PreviousChain

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testE` and `lem:print`, paper/paper.tex: both original nonnegative chain summands are read before
the retained rate is applied to their signed difference. -/
def readDigitPair (store : Fin MM) : St VV MM :=
  .seq (readChainRecord store linearPositive) (readPreviousChain store)

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the complete digit pair is physically
loaded from the proposed chain, including the first row's zero term
and every later predecessor, without a decoded-coefficient oracle. -/
theorem readDigitPair_run (C : Ctx) (store : Fin MM)
    (G row J k g : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G) (hr : a.env chainRow=row)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd) :
    Hs C (readDigitPair store) a (a.rc store+11*bits.length+71) (fun z=>
      z.env linearPositive=(if row<J then (bits.getD ((row+1)*G+k+g) false).toNat else 0) ∧
      z.env linearNegative=(if row=0 then 0 else
        if row-1<J then (bits.getD (row*G+k+g) false).toNat else 0) ∧
      z.env chainRow=row ∧
      StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      z.rc store≤bits.length ∧ Cst z ∧
      Fr a z [savedChainRow,chainRow,linearPositive,linearNegative,sourceRecordLimit,
        atomValue,sourceRecordIndex,sourceRecordDiscard]) := by
  unfold readDigitPair
  apply Hx.hs
  refine Hs.then (readChainRecord_source C store linearPositive (by decide)
    G row J k g bits a hc hG hgG hb hr hJ hk hg hram hcursor hbits hbound)
    (fun b ⟨bp,bs,br,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine Hs.last (readPreviousChain_run C store G row J k g bits b bc hG hgG
    ((bfr _ (by decide)).trans hb) ((bfr _ (by decide)).trans hr)
    ((bfr _ (by decide)).trans hJ) ((bfr _ (by decide)).trans hk)
    ((bfr _ (by decide)).trans hg) (by rw [bram]; exact hram)
    br hbits hbound)
    (fun z ⟨zn,zrow,zs,zr,zc,zfr⟩ n2 hn2=>?_)
  refine ⟨⟨(zfr _ (by decide)).trans bp,zn,zrow,zs.trans bs,zr,zc,
    (bfr.weaken (by decide)).trans (zfr.weaken (by decide))⟩,?_⟩
  omega

end NearQuarticWires.StageCert.Tokens
