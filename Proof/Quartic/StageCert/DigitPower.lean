import Proof.Quartic.StageCert.DigitWalkForm
import Proof.Quartic.StageCert.MomentExponent

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testE` and `lem:print`, paper/paper.tex: serialize the complete original digit and its literal
m=4 even moment, using the physically computed exponent 8k. -/
def emitDigitPower (witnessStore ratesStore : Fin MM) : St VV MM :=
  .seq prepareWalkExponent (.seq (emitDigitWalkForm witnessStore ratesStore) (emitPower momentExponent))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the actual signed digit moment power
uses every original occurrence and its full retained coefficient on
all formal assignments, with no passing-column premise. -/
theorem emitDigitPower_run (C : Ctx) (witnessStore ratesStore : Fin MM)
    (hne : witnessStore≠ratesStore) (G row J k circuit firstCount code Bcoef Batom : ℕ)
    (bits : List Bool) (factors : List ℕ) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hb : a.env atomCount=G) (hr : a.env requestedChainRow=row)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k)
    (hcirc : a.env selectedCircuit=circuit) (hfirst : a.env firstGateCount=firstCount)
    (hcode : a.env newtonTau=code) (hrow : row<J) (hlen : factors.length=J-1)
    (hram : a.ram witnessStore=bits.map Bool.toNat) (hfr : a.ram ratesStore=factors)
    (hcursor : a.rc witnessStore≤bits.length) (hfcur : a.rc ratesStore≤factors.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd)
    (hfit : J≤2^C.Wd)
    (hratefit : (if row=0 then 1 else factors.getD (row-1) 0)<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : ∀g<G,natBitLength (((selectedSummand circuit firstCount g
      (sourceDigitPositive bits G row J k g):ℤ)-selectedSummand circuit firstCount g
      (sourceDigitNegative bits factors G row J k g)).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) (hexp : 8*k<2^C.Wd)
    (hexpWord : natBitLength (8*k)+2<2^C.Wd) :
    Hs C (emitDigitPower witnessStore ratesStore) a
      (G*(12*bits.length+6*factors.length+8*(40*Bcoef+160*Batom+640)+160)+
        40*natBitLength (8*k)+110) (fun z=>
      z.out=a.out++(toks (Formula.pow
        (sourceDigitWalkFormula G row J k circuit firstCount code bits factors) (8*k))).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc witnessStore≤bits.length ∧ z.rc ratesStore≤factors.length ∧ Cst z ∧
      Fr a z (momentExponent::atomOccurrence::digitOccurrenceScratch)) := by
  unfold emitDigitPower
  apply Hx.hs
  refine Hs.then (prepareWalkExponent_run C k a hc hk hexp)
    (fun b ⟨bexp,bs,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  have brc : b.rc=a.rc := congrArg (fun q=>q.2.2.2.1) bs
  refine Hs.then (emitDigitWalkForm_run C witnessStore ratesStore hne
    G row J k circuit firstCount code Bcoef Batom bits factors b bc hG
    ((bfr _ (by decide)).trans hb) ((bfr _ (by decide)).trans hr)
    ((bfr _ (by decide)).trans hJ) ((bfr _ (by decide)).trans hk)
    ((bfr _ (by decide)).trans hcirc) ((bfr _ (by decide)).trans hfirst)
    ((bfr _ (by decide)).trans hcode) hrow hlen
    (by rw [bram]; exact hram) (by rw [bram]; exact hfr)
    (by rw [brc]; exact hcursor) (by rw [brc]; exact hfcur)
    hbits hbound hfit hratefit hW hindex hB hAtomFit hCoef hCoefFit)
    (fun d ⟨doo,ds,dw,dr,dc,dfr⟩ n2 hn2=>?_)
  have dexp : d.env momentExponent=8*k := (dfr _ (by decide)).trans bexp
  refine Hs.last (emitPower_run C momentExponent (by decide) (by decide) d dc (by omega)
    (by rw [dexp]; exact hexpWord))
    (fun z ⟨zo,zs,zc,zfr⟩ n3 hn3=>?_)
  have bo : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have zr : z.rc=d.rc := congrArg (fun q=>q.2.2.1) zs
  refine ⟨⟨?_,?_,by rw [zr]; exact dw,by rw [zr]; exact dr,zc,
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide) |>.trans (zfr.weaken (by decide)))⟩,?_⟩
  · rw [zo,doo,bo,dexp]
    simp only [toks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  · simp only [DS.sh,Prod.mk.injEq] at bs
    simp only [Prod.mk.injEq] at ds zs ⊢
    exact ⟨zs.1.trans (ds.1.trans bs.1),zs.2.1.trans (ds.2.1.trans bs.2.2.1),
      zs.2.2.2.1.trans (ds.2.2.1.trans bs.2.2.2.2.1),
      zs.2.2.2.2.1.trans (ds.2.2.2.1.trans bs.2.2.2.2.2.1),
      zs.2.2.2.2.2.trans (ds.2.2.2.2.trans bs.2.2.2.2.2.2)⟩
  · rw [dexp] at hn3
    omega

end NearQuarticWires.StageCert.Tokens
