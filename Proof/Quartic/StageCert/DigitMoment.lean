import Proof.Quartic.StageCert.CompleteWalkMasks
import Proof.Quartic.StageCert.DigitPower
import Proof.Quartic.StageCert.LinearParameters
import Proof.Quartic.StageLift.PrintFrames

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator
open NearQuarticWires.StageLift

/-- `eq:testE` and `lem:print`, paper/paper.tex: the complete original tuple-mask digit moment on its
unchanged seventeen-role occurrence pool. -/
def sourceDigitMomentFormula (G row J k circuit firstCount code tau X : ℕ)
    (bits : List Bool) (factors : List ℕ) (structural : Fin 8→Bool) : Formula (17*G) :=
  .mul (completeWalkMaskFormula G tau X k bits structural)
    (.pow (sourceDigitWalkFormula G row J k circuit firstCount code bits factors) (8*k))

/-- `lem:print`, paper/paper.tex: complete moment
source scratch, excluding the persistent original-call/controller fields. -/
def momentSourceScratch : List (Fin VV) :=
  [t2,c0,vJ,newtonTau,maskLimit,selectionStart,maskStructural,newtonIndex]++maskDegreeScratch++
    [chainRows,finalScale,finalOffset,requestedChainRow,momentExponent,atomOccurrence]++digitOccurrenceScratch

/-- `eq:testE` and `lem:print`, paper/paper.tex: read actual selected parameters, emit every original mask,
reload the original signed digit metadata, and close its exact moment. -/
def emitDigitMoment : St VV MM :=
  .seq loadMaskParameters (.seq (emitCompleteWalkMasks witnessStore)
    (.seq loadLinearParameters (.seq (emitDigitPower witnessStore factorStore)
      (StageLift.emitOperator .mul))))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the entire digit moment is generated
by actual selected-parameter reads, literal structural-source reads,
retained-witness/rate arithmetic and original integer Formula output.
All bad columns and every exact zero coefficient retain their full value. -/
theorem emitDigitMoment_run (C : Ctx) (p : Cells.Parameters)
    (G row circuit firstCount code Bcoef Batom Bnewton : ℕ)
    (bits : List Bool) (structural : Fin 8→Bool) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a) (hG : 1≤G) (hb : a.env atomCount=G)
    (hr : a.env requestedChainRow=row) (hcirc : a.env selectedCircuit=circuit)
    (hfirst : a.env firstGateCount=firstCount) (hcode : a.env sourceSignOrdinal=code)
    (htag : a.env sourceTestTag=1) (hrow : row<p.J) (hJpos : 1≤p.J)
    (hin : C.inp.drop a.ip=List.ofFn structural++rest)
    (hparams : a.ram parameterStore=parameterScalars p)
    (hwitness : a.ram witnessStore=bits.map Bool.toNat) (hfactors : a.ram factorStore=p.factors)
    (hfLen : p.factors.length=p.J-1)
    (hRC : ∀m,a.rc m≤(a.ram m).length) (hKC : a.kc≤a.kout.length)
    (hbits : p.k+(p.J+1)*G≤bits.length) (haddress : p.k+(p.J+1)*G≤2^C.Wd)
    (hfit : 2*G^p.Xmax≤2^C.Wd) (hwidth : 2*p.Xmax+2≤C.Wd)
    (hW : 6≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hBn : ∀degree≤p.Xmax,natBitLength (Mask.newtonCoeff p.tau degree).natAbs≤Bnewton)
    (hNewtonFit : Bnewton+2<2^C.Wd) (hJfit : p.J≤2^C.Wd)
    (hRateFit : (if row=0 then 1 else p.factors.getD (row-1) 0)<2^C.Wd)
    (hCoef : ∀g<G,natBitLength (((selectedSummand circuit firstCount g
      (sourceDigitPositive bits G row p.J p.k g):ℤ)-selectedSummand circuit firstCount g
      (sourceDigitNegative bits p.factors G row p.J p.k g)).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) (hexp : 8*p.k<2^C.Wd)
    (hexpWord : natBitLength (8*p.k)+2<2^C.Wd) :
    Hs C emitDigitMoment a
      (completeMaskSourceCost G p.k p.Xmax Batom Bnewton bits.length+
        G*(12*bits.length+6*p.factors.length+8*(40*Bcoef+160*Batom+640)+160)+
        40*natBitLength (8*p.k)+1510) (fun z=>
      z.out=a.out++(toks (sourceDigitMomentFormula G row p.J p.k circuit firstCount code
        p.tau p.Xmax bits p.factors structural)).flatMap tokWord ∧
      z.ip=a.ip+8 ∧ (z.ram,z.kin,z.kout,z.kc)=(a.ram,a.kin,a.kout,a.kc) ∧
      z.rc witnessStore≤bits.length ∧ z.rc factorStore≤p.factors.length ∧
      Cst z ∧ Fr a z momentSourceScratch) := by
  have hspan : G≤(p.J+1)*G := Nat.le_mul_of_pos_left _ (by omega)
  have hcur : a.rc parameterStore≤46 := by
    simpa only [hparams,parameterScalars_length] using hRC parameterStore
  have hXfit : p.Xmax+1<2^C.Wd :=
    (show p.Xmax+1<C.Wd by omega).trans Nat.lt_two_pow_self
  unfold emitDigitMoment
  apply Hx.hs
  refine Hs.then ((loadMaskParameters_run C p a hc hparams (by omega) hXfit).rc_le hRC hKC)
    (fun b ⟨⟨bt,bX,bk,_,bs,bc,bfr⟩,bRC,bKC⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  have bip : b.ip=a.ip := congrArg Prod.fst bs
  refine Hs.then ((emitCompleteWalkMasks_run C witnessStore G p.tau p.Xmax p.k Batom Bnewton
    bits structural rest b bc hG (by rw [bip]; exact hin)
    ((bfr _ (by decide)).trans hb) bt bX bk (by rw [bram]; exact hwitness)
    (by simpa only [bram,hwitness,List.length_map] using bRC witnessStore)
    (by omega) (by omega) hfit hwidth (by omega) hindex hB hAtomFit hBn hNewtonFit).rc_le bRC bKC)
    (fun d ⟨⟨doo,di,ds,_,dc,dfr⟩,dRC,dKC⟩ n2 hn2=>?_)
  have dram : d.ram=a.ram := (congrArg Prod.fst ds).trans bram
  have df : Fr a d momentSourceScratch :=
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
  have dcur : d.rc parameterStore≤46 := by
    simpa only [dram,hparams,parameterScalars_length] using dRC parameterStore
  refine Hs.then ((loadLinearParameters_run C p d dc (by rw [dram]; exact hparams)
    hW hJpos).rc_le dRC dKC)
    (fun e ⟨⟨eJ,_,_,ecode,erow,_,es,ec,efr⟩,eRC,_⟩ n3 hn3=>?_)
  have eram : e.ram=a.ram := (congrArg (fun q=>q.2.2.1) es).trans dram
  have ef : Fr a e momentSourceScratch := df.trans (efr.weaken (by decide))
  have drow : d.env requestedChainRow=row :=
    (dfr _ (by decide)).trans ((bfr _ (by decide)).trans hr)
  have dtag : d.env sourceTestTag=1 := (df _ (by decide)).trans htag
  have er : e.env requestedChainRow=row := by
    rw [erow,dtag,if_pos rfl,drow]
  have ek : e.env selectionStart=p.k := (efr _ (by decide)).trans ((dfr _ (by decide)).trans bk)
  have ecod : e.env newtonTau=code := ecode.trans ((df _ (by decide)).trans hcode)
  refine Hs.then (emitDigitPower_run C witnessStore factorStore (by decide)
    G row p.J p.k circuit firstCount code Bcoef Batom bits p.factors e ec hG
    ((ef _ (by decide)).trans hb) er eJ ek ((ef _ (by decide)).trans hcirc)
    ((ef _ (by decide)).trans hfirst) ecod hrow hfLen
    (by rw [eram]; exact hwitness) (by rw [eram]; exact hfactors)
    (by simpa only [eram,hwitness,List.length_map] using eRC witnessStore)
    (by simpa only [eram,hfactors] using eRC factorStore)
    hbits haddress hJfit hRateFit (by omega) hindex hB hAtomFit hCoef hCoefFit hexp hexpWord)
    (fun f ⟨fo,fs,fw,fr,fc,ffr⟩ n4 hn4=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .mul f fc)
    (fun z ⟨zo,zs,zc,zfr⟩ n5 hn5=>?_)
  have eo : e.out=d.out := congrArg (fun q=>q.2.1) es
  have bo : b.out=a.out := congrArg (fun q=>q.2.1) bs
  have zr : z.rc=f.rc := congrArg (fun q=>q.2.2.1) zs
  have eip : e.ip=d.ip := congrArg Prod.fst es
  refine ⟨⟨?_,?_,?_,by rw [zr]; exact fw,by rw [zr]; exact fr,zc,
    ef.trans ((ffr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  · rw [zo,fo,eo,doo,bo]
    simp only [sourceDigitMomentFormula,toks,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]
  · exact (congrArg Prod.fst zs).trans ((congrArg Prod.fst fs).trans (eip.trans (di.trans (by omega))))
  · simp only [StageMain.parameterRest,Prod.mk.injEq] at es bs
    simp only [Prod.mk.injEq] at zs fs ds ⊢
    exact ⟨zs.2.1.trans (fs.2.1.trans eram),
      zs.2.2.2.1.trans (fs.2.2.1.trans (es.2.2.2.2.1.trans (ds.2.1.trans bs.2.2.2.2.1))),
      zs.2.2.2.2.1.trans (fs.2.2.2.1.trans (es.2.2.2.2.2.1.trans (ds.2.2.1.trans bs.2.2.2.2.2.1))),
      zs.2.2.2.2.2.trans (fs.2.2.2.2.trans (es.2.2.2.2.2.2.trans (ds.2.2.2.trans bs.2.2.2.2.2.2)))⟩
  · have hm : 2*(tokWord Tok.mul).length+1=15 := by decide
    rw [hm] at hn5
    omega

end NearQuarticWires.StageCert.Tokens
