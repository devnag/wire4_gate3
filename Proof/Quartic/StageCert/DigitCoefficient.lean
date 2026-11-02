import Proof.Quartic.StageCert.DigitScale

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testE` and `lem:print`, paper/paper.tex: the first digit's predecessor is zero and all later
predecessors are literal retained Boolean chain records. -/
def predecessorBit (bits : List Bool) (G row J k g : ℕ) : ℕ :=
  if row=0 then 0 else if row-1<J then (bits.getD (row*G+k+g) false).toNat else 0

/-- `eq:testE`, paper/paper.tex: the original predecessor
is a bit even when its row is absent or its requested digit is zero. -/
theorem predecessorBit_le_one (bits : List Bool) (G row J k g : ℕ) :
    predecessorBit bits G row J k g≤1 := by
  unfold predecessorBit
  split_ifs <;> first | omega | cases bits.getD (row*G+k+g) false <;> decide

/-- `lem:print` and `prop:time`, paper/paper.tex: source coefficient arithmetic retains the input, emitted
tokens, all physical record data and every callee stream. -/
def coefficientSourceRest (a : DS VV MM) := (a.ip,a.out,a.ram,a.kin,a.kout,a.kc)

/-- `eq:testE` and `lem:print`, paper/paper.tex: load the complete original digit coefficient from two
retained chain bits and the actual active integer rate. -/
def loadDigitCoefficient (witnessStore ratesStore : Fin MM) : St VV MM :=
  .seq (readDigitPair witnessStore)
    (.seq (readDigitRate ratesStore) scaleDigitNegative)

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the signed coefficient's two natural
summands are produced by physical reads and binary multiplication.
Every original source record and all exact zero differences survive. -/
theorem loadDigitCoefficient_run (C : Ctx) (witnessStore ratesStore : Fin MM)
    (hne : witnessStore≠ratesStore) (G row J k g : ℕ) (bits : List Bool)
    (factors : List ℕ) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hgG : g<G) (hb : a.env atomCount=G) (hr : a.env chainRow=row)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k) (hg : a.env atomOccurrence=g)
    (hrow : row<J) (hlen : factors.length=J-1)
    (hram : a.ram witnessStore=bits.map Bool.toNat) (hfr : a.ram ratesStore=factors)
    (hcursor : a.rc witnessStore≤bits.length) (hfcur : a.rc ratesStore≤factors.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd)
    (hfit : J≤2^C.Wd)
    (hratefit : (if row=0 then 1 else factors.getD (row-1) 0)<2^C.Wd) :
    Hs C (loadDigitCoefficient witnessStore ratesStore) a
      (a.rc witnessStore+a.rc ratesStore+11*bits.length+5*factors.length+100) (fun z=>
      z.env linearPositive=(if row<J then (bits.getD ((row+1)*G+k+g) false).toNat else 0) ∧
      z.env linearNegative=predecessorBit bits G row J k g*
        (if row=0 then 1 else factors.getD (row-1) 0) ∧
      coefficientSourceRest z=coefficientSourceRest a ∧
      z.rc witnessStore≤bits.length ∧ z.rc ratesStore≤factors.length ∧ Cst z ∧
      Fr a z [savedChainRow,chainRow,linearPositive,linearNegative,linearRate,linearProduct,
        sourceRecordLimit,atomValue,sourceRecordIndex,sourceRecordDiscard]) := by
  unfold loadDigitCoefficient
  apply Hx.hs
  refine Hs.then (readDigitPair_run C witnessStore G row J k g bits a hc hG hgG
    hb hr hJ hk hg hram hcursor hbits hbound)
    (fun b ⟨bp,bn,brow,bs,br,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  have bfrc : b.rc ratesStore=a.rc ratesStore := by
    have hh := congrArg (fun q=>q.2.2.2.1 ratesStore) bs
    simpa [StageLift.memorySourceRest,Function.update_of_ne (Ne.symm hne)] using hh
  refine Hs.then (readDigitRate_run C ratesStore row J factors b bc brow hrow hlen
    (by rw [bram]; exact hfr) (by rw [bfrc]; exact hfcur) hfit)
    (fun d ⟨drate,ds,drc,dc,dfr⟩ n2 hn2=>?_)
  have dwr : d.rc witnessStore=b.rc witnessStore := by
    have hh := congrArg (fun q=>q.2.2.2.1 witnessStore) ds
    simpa [StageLift.memorySourceRest,Function.update_of_ne hne] using hh
  have dp : d.env linearPositive=(if row<J then
      (bits.getD ((row+1)*G+k+g) false).toNat else 0) := (dfr _ (by decide)).trans bp
  have dn : d.env linearNegative=predecessorBit bits G row J k g :=
    (dfr _ (by decide)).trans bn
  refine Hs.last (scaleDigitNegative_run C (predecessorBit bits G row J k g)
    (if row=0 then 1 else factors.getD (row-1) 0) d dc dn drate
    (predecessorBit_le_one bits G row J k g) hratefit)
    (fun z ⟨zn,zs,zc,zfr⟩ n3 hn3=>?_)
  have zrc : z.rc=d.rc := congrArg (fun q=>q.2.2.2.1) zs
  refine ⟨⟨(zfr _ (by decide)).trans dp,zn,?_,by rw [zrc,dwr]; exact br,
    by rw [zrc]; exact drc,zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  · simp only [StageLift.memorySourceRest,DS.sh,coefficientSourceRest,Prod.mk.injEq] at bs ds zs ⊢
    exact ⟨zs.1.trans (ds.1.trans bs.1),zs.2.1.trans (ds.2.1.trans bs.2.1),
      zs.2.2.1.trans (ds.2.2.1.trans bs.2.2.1),
      zs.2.2.2.2.1.trans (ds.2.2.2.2.1.trans bs.2.2.2.2.1),
      zs.2.2.2.2.2.1.trans (ds.2.2.2.2.2.1.trans bs.2.2.2.2.2.1),
      zs.2.2.2.2.2.2.trans (ds.2.2.2.2.2.2.trans bs.2.2.2.2.2.2)⟩
  · rw [bfrc] at hn2
    omega

end NearQuarticWires.StageCert.Tokens
