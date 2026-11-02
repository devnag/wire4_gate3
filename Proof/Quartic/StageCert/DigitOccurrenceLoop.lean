import Proof.Quartic.StageCert.DigitOccurrence

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testE` and `lem:print`, paper/paper.tex: the literal original-bank occurrence list of a digit form. -/
def sourceDigitOccurrenceForms (G row J k circuit firstCount code : ℕ)
    (bits : List Bool) (factors : List ℕ) : List (Formula (17*G)) :=
  List.ofFn fun g : Fin G=>occurrenceWalkFormula G g.val g.isLt
    ((selectedSummand circuit firstCount g.val (sourceDigitPositive bits G row J k g.val):ℤ)-
      selectedSummand circuit firstCount g.val (sourceDigitNegative bits factors G row J k g.val)) code

/-- `lem:print`, paper/paper.tex: enumerate the
actual concatenated original occurrences, preserving repeated labels. -/
def emitDigitOccurrences (witnessStore ratesStore : Fin MM) : St VV MM :=
  forS atomOccurrence atomCount (emitDigitOccurrence witnessStore ratesStore)

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the full original occurrence stream is
physically serialized from retained chain bits and rates. The runtime
charges every source scan and all eight edges of every actual occurrence. -/
theorem emitDigitOccurrences_run (C : Ctx) (witnessStore ratesStore : Fin MM)
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
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C (emitDigitOccurrences witnessStore ratesStore) a
      (G*(12*bits.length+6*factors.length+8*(40*Bcoef+160*Batom+640)+144)+4) (fun z=>
      z.out=a.out++(sourceDigitOccurrenceForms G row J k circuit firstCount code bits factors).flatMap
        (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc witnessStore≤bits.length ∧ z.rc ratesStore≤factors.length ∧ Cst z ∧
      Fr a z (atomOccurrence::digitOccurrenceScratch)) := by
  let fs := sourceDigitOccurrenceForms G row J k circuit firstCount code bits factors
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.out=a.out++factorPrefix fs i ∧
    (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
    b.rc witnessStore≤bits.length ∧ b.rc ratesStore≤factors.length ∧ Cst b ∧
    Fr a b (atomOccurrence::digitOccurrenceScratch)
  have hset : ∀ i b v,I i b→I i (b.set atomOccurrence v) := by
    rintro i b v ⟨bo,bs,bw,br,bc,bfr⟩
    exact ⟨bo,bs,bw,br,Cst.of_fr (T := [atomOccurrence]) bc (Fr.set _ _ (by simp)) (by decide),
      bfr.trans (Fr.set _ _ (by simp))⟩
  have hGfit : G<2^C.Wd := by omega
  unfold emitDigitOccurrences
  refine (forS_spec' (C := C) atomOccurrence atomCount (by decide)
    (emitDigitOccurrence witnessStore ratesStore) a G hGfit I
    (12*bits.length+6*factors.length+8*(40*Bcoef+160*Batom+640)+140) hset
    ⟨by simp [factorPrefix],rfl,hcursor,hfcur,hc,Fr.refl _ _⟩ hb ?_).mono le_rfl ?_
  · intro i hi b ⟨bo,bs,bw,br,bc,bfr⟩ bi bn
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
    refine (emitDigitOccurrence_run C witnessStore ratesStore hne
      G row J k i circuit firstCount code Bcoef Batom bits factors b bc hG hi bn
      ((bfr _ (by decide)).trans hr) ((bfr _ (by decide)).trans hJ)
      ((bfr _ (by decide)).trans hk) bi ((bfr _ (by decide)).trans hcirc)
      ((bfr _ (by decide)).trans hfirst) ((bfr _ (by decide)).trans hcode) hrow hlen
      (by rw [bram]; exact hram) (by rw [bram]; exact hfr) bw br hbits hbound hfit
      hratefit hW hindex (hB i hi) hAtomFit (hCoef i hi) hCoefFit).mono (by omega) ?_
    rintro z ⟨zo,zs,zw,zr,zc,zfr⟩
    have hil : i<fs.length := by simpa [fs,sourceDigitOccurrenceForms] using hi
    have zform : z.out=b.out++(toks fs[i]).flatMap tokWord := by
      simpa only [fs,sourceDigitOccurrenceForms,List.getElem_ofFn] using zo
    refine ⟨⟨?_,zs.trans bs,zw,zr,zc,
      bfr.trans (zfr.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx))⟩,?_,?_⟩
    · rw [zform,bo]
      simp only [factorPrefix,List.take_succ_eq_append_getElem hil,List.flatMap_append,
        List.flatMap_singleton,List.append_assoc]
    · rw [zfr _ (by decide)]
      exact bi
    · rw [zfr _ (by decide)]
      exact bn
  · rintro z ⟨⟨zo,zs,zw,zr,zc,zfr⟩,_,_⟩
    refine ⟨?_,zs,zw,zr,zc,zfr⟩
    have htake : fs.take G=fs := List.take_of_length_le (by simp [fs,sourceDigitOccurrenceForms])
    simpa only [factorPrefix,htake] using zo

end NearQuarticWires.StageCert.Tokens
