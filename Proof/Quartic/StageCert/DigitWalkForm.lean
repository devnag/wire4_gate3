import Proof.Quartic.StageCert.DigitOccurrenceLoop

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the original
linear-form sum has a literal zero and one closing addition per term. -/
theorem originalSumList_tokens {V : ℕ} (fs : List (Formula V)) :
    toks (Formula.sumList fs)=fs.flatMap toks++[.const 0]++List.replicate fs.length .add := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [Formula.sumList,toks,ih,List.flatMap_cons,List.length_cons]
    rw [List.replicate_succ']
    simp only [List.append_assoc]

/-- `eq:testE` and `lem:print`, paper/paper.tex: the full proposed-digit linear form on the unchanged
original seventeen-role occurrence pool. -/
def sourceDigitWalkFormula (G row J k circuit firstCount code : ℕ)
    (bits : List Bool) (factors : List ℕ) : Formula (17*G) :=
  Formula.sumList (sourceDigitOccurrenceForms G row J k circuit firstCount code bits factors)

/-- `lem:print`, paper/paper.tex: close the actual
original occurrence stream by a zero and one addition per occurrence. -/
def emitDigitWalkForm (witnessStore ratesStore : Fin MM) : St VV MM :=
  .seq (emitDigitOccurrences witnessStore ratesStore)
    (.seq (StageLift.emitOperator (.const 0))
      (.seq (.op (.copy sourceRecordLimit atomCount)) (emitCopies .add)))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: the complete original digit form is a
physically emitted integer Formula, with actual witness/factor reads,
all signed coefficients, repeated occurrences and all original source
records retained. This endpoint does not assume any certified column. -/
theorem emitDigitWalkForm_run (C : Ctx) (witnessStore ratesStore : Fin MM)
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
    Hs C (emitDigitWalkForm witnessStore ratesStore) a
      (G*(12*bits.length+6*factors.length+8*(40*Bcoef+160*Batom+640)+160)+40) (fun z=>
      z.out=a.out++(toks (sourceDigitWalkFormula G row J k circuit firstCount code bits factors)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc witnessStore≤bits.length ∧ z.rc ratesStore≤factors.length ∧ Cst z ∧
      Fr a z (atomOccurrence::digitOccurrenceScratch)) := by
  have hGfit : G<2^C.Wd := by omega
  unfold emitDigitWalkForm
  apply Hx.hs
  refine Hs.then (emitDigitOccurrences_run C witnessStore ratesStore hne
    G row J k circuit firstCount code Bcoef Batom bits factors a hc hG hb hr hJ hk
    hcirc hfirst hcode hrow hlen hram hfr hcursor hfcur hbits hbound hfit hratefit
    hW hindex hB hAtomFit hCoef hCoefFit)
    (fun b ⟨bo,bs,bw,br,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (StageLift.emitOperator_spec C (.const 0) b bc)
    (fun d ⟨doo,ds,dc,dfr⟩ n2 hn2=>?_)
  refine Hs.then (hs_copy C sourceRecordLimit atomCount d (by decide))
    (fun e he n3 hn3=>?_)
  subst he
  let e := d.set sourceRecordLimit (d.env atomCount)
  have dG : d.env atomCount=G := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans hb)
  have ec : Cst e := Cst.of_fr (T := [sourceRecordLimit]) dc (Fr.set _ _ (by simp)) (by decide)
  have eG : e.env sourceRecordLimit=G := by change d.env atomCount=G; exact dG
  refine Hs.last (emitCopies_run C .add e ec G eG hGfit)
    (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
  have zr : z.rc=b.rc := (congrArg (fun q=>q.2.2.1) zs).trans (congrArg (fun q=>q.2.2.1) ds)
  have zsrc : (z.ip,z.ram,z.kin,z.kout,z.kc)=(b.ip,b.ram,b.kin,b.kout,b.kc) := by
    simp only [Prod.mk.injEq] at zs ds ⊢
    exact ⟨zs.1.trans ds.1,zs.2.1.trans ds.2.1,
      zs.2.2.2.1.trans ds.2.2.2.1,zs.2.2.2.2.1.trans ds.2.2.2.2.1,
      zs.2.2.2.2.2.trans ds.2.2.2.2.2⟩
  refine ⟨⟨?_,zsrc.trans bs,by rw [zr]; exact bw,by rw [zr]; exact br,zc,
    bfr.trans ((dfr.weaken (by decide)).trans
      ((Fr.set _ _ (by decide)).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zo]
    change d.out++_=_
    rw [doo,bo]
    have htoks : toks (sourceDigitWalkFormula G row J k circuit firstCount code bits factors)=
      (sourceDigitOccurrenceForms G row J k circuit firstCount code bits factors).flatMap toks++
        [.const 0]++List.replicate G .add := by
      simpa only [sourceDigitWalkFormula,sourceDigitOccurrenceForms,List.length_ofFn] using
        (originalSumList_tokens (sourceDigitOccurrenceForms G row J k circuit firstCount code bits factors))
    rw [htoks]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.flatMap_assoc,List.append_assoc]
  · have hz : (tokWord (.const 0)).length=9 := by decide
    have ha : (tokWord .add).length=5 := by decide
    rw [hz] at hn2
    rw [ha] at hn4
    nlinarith only [hn1,hn2,hn3,hn4]

end NearQuarticWires.StageCert.Tokens
