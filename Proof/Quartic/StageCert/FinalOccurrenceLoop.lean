import Proof.Quartic.StageCert.FinalOccurrence

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the literal original occurrence list of the final-error form. -/
def sourceFinalOccurrenceForms (G J k M A circuit firstCount code : ℕ)
    (bits : List Bool) : List (Formula (17*G)) :=
  List.ofFn fun g : Fin G=>occurrenceWalkFormula G g.val g.isLt
    ((selectedSummand circuit firstCount g.val (sourceFinalPositive bits G J k g.val M):ℤ)-
      selectedSummand circuit firstCount g.val A) code

/-- `lem:print`, paper/paper.tex: enumerate all
original final-error occurrences, including every repeated physical label. -/
def emitFinalOccurrences (store : Fin MM) : St VV MM :=
  forS atomOccurrence atomCount (emitFinalOccurrence store)

/-- `eq:testPhi`, `lem:print` and `prop:time`, paper/paper.tex: all original final-error
occurrences and their complete signed eight-edge contributions are
serialized by an actual loop over the original retained witness. -/
theorem emitFinalOccurrences_run (C : Ctx) (store : Fin MM)
    (G J k M A circuit firstCount code Bcoef Batom : ℕ)
    (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hb : a.env atomCount=G) (hr : a.env requestedChainRow=J-1)
    (hJ : a.env chainRows=J) (hk : a.env selectionStart=k)
    (hM : a.env finalScale=M) (hA : a.env finalOffset=A)
    (hcirc : a.env selectedCircuit=circuit) (hfirst : a.env firstGateCount=firstCount)
    (hcode : a.env newtonTau=code)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+(J+1)*G≤bits.length) (hbound : k+(J+1)*G≤2^C.Wd)
    (hfit : M<2^C.Wd) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd)
    (hCoef : ∀g<G,natBitLength (((selectedSummand circuit firstCount g
      (sourceFinalPositive bits G J k g M):ℤ)-selectedSummand circuit firstCount g A).natAbs)≤Bcoef)
    (hCoefFit : Bcoef+2<2^C.Wd) :
    Hs C (emitFinalOccurrences store) a
      (G*(6*bits.length+8*(40*Bcoef+160*Batom+640)+84)+4) (fun z=>
      z.out=a.out++(sourceFinalOccurrenceForms G J k M A circuit firstCount code bits).flatMap
        (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (atomOccurrence::digitOccurrenceScratch)) := by
  let fs := sourceFinalOccurrenceForms G J k M A circuit firstCount code bits
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.out=a.out++factorPrefix fs i ∧
    (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
    b.rc store≤bits.length ∧ Cst b ∧ Fr a b (atomOccurrence::digitOccurrenceScratch)
  have hset : ∀ i b v,I i b→I i (b.set atomOccurrence v) := by
    rintro i b v ⟨bo,bs,br,bc,bfr⟩
    exact ⟨bo,bs,br,Cst.of_fr (T := [atomOccurrence]) bc (Fr.set _ _ (by simp)) (by decide),
      bfr.trans (Fr.set _ _ (by simp))⟩
  have hGfit : G<2^C.Wd := by omega
  unfold emitFinalOccurrences
  refine (forS_spec' (C := C) atomOccurrence atomCount (by decide)
    (emitFinalOccurrence store) a G hGfit I
    (6*bits.length+8*(40*Bcoef+160*Batom+640)+80) hset
    ⟨by simp [factorPrefix],rfl,hcursor,hc,Fr.refl _ _⟩ hb ?_).mono le_rfl ?_
  · intro i hi b ⟨bo,bs,br,bc,bfr⟩ bi bn
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
    refine (emitFinalOccurrence_run C store G J k i M A circuit firstCount code Bcoef Batom
      bits b bc hG hi bn ((bfr _ (by decide)).trans hr) ((bfr _ (by decide)).trans hJ)
      ((bfr _ (by decide)).trans hk) bi ((bfr _ (by decide)).trans hM)
      ((bfr _ (by decide)).trans hA) ((bfr _ (by decide)).trans hcirc)
      ((bfr _ (by decide)).trans hfirst) ((bfr _ (by decide)).trans hcode)
      (by rw [bram]; exact hram) br hbits hbound hfit hW hindex
      (hB i hi) hAtomFit (hCoef i hi) hCoefFit).mono (by omega) ?_
    rintro z ⟨zo,zs,zr,zc,zfr⟩
    have hil : i<fs.length := by simpa [fs,sourceFinalOccurrenceForms] using hi
    have zform : z.out=b.out++(toks fs[i]).flatMap tokWord := by
      simpa only [fs,sourceFinalOccurrenceForms,List.getElem_ofFn] using zo
    refine ⟨⟨?_,zs.trans bs,zr,zc,
      bfr.trans (zfr.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx))⟩,?_,?_⟩
    · rw [zform,bo]
      simp only [factorPrefix,List.take_succ_eq_append_getElem hil,List.flatMap_append,
        List.flatMap_singleton,List.append_assoc]
    · rw [zfr _ (by decide)]
      exact bi
    · rw [zfr _ (by decide)]
      exact bn
  · rintro z ⟨⟨zo,zs,zr,zc,zfr⟩,_,_⟩
    refine ⟨?_,zs,zr,zc,zfr⟩
    have htake : fs.take G=fs := List.take_of_length_le (by simp [fs,sourceFinalOccurrenceForms])
    simpa only [factorPrefix,htake] using zo

end NearQuarticWires.StageCert.Tokens
