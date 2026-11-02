import Proof.Quartic.StageCert.FinalOccurrenceLoop
import Proof.Quartic.StageCert.DigitWalkForm

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the complete final-error linear form on the unchanged
seventeen-role original occurrence pool. -/
def sourceFinalWalkFormula (G J k M A circuit firstCount code : ℕ)
    (bits : List Bool) : Formula (17*G) :=
  Formula.sumList (sourceFinalOccurrenceForms G J k M A circuit firstCount code bits)

/-- `lem:print`, paper/paper.tex: close all original
final-error occurrences with their literal zero and addition tokens. -/
def emitFinalWalkForm (store : Fin MM) : St VV MM :=
  .seq (emitFinalOccurrences store) (.seq (StageLift.emitOperator (.const 0))
    (.seq (.op (.copy sourceRecordLimit atomCount)) (emitCopies .add)))

/-- `eq:testPhi`, `lem:print` and `prop:time`, paper/paper.tex: the complete original
final-error form is emitted by physical witness reads and exact signed
arithmetic on every original occurrence, with no certification premise. -/
theorem emitFinalWalkForm_run (C : Ctx) (store : Fin MM)
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
    Hs C (emitFinalWalkForm store) a
      (G*(6*bits.length+8*(40*Bcoef+160*Batom+640)+100)+40) (fun z=>
      z.out=a.out++(toks (sourceFinalWalkFormula G J k M A circuit firstCount code bits)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (atomOccurrence::digitOccurrenceScratch)) := by
  have hGfit : G<2^C.Wd := by omega
  unfold emitFinalWalkForm
  apply Hx.hs
  refine Hs.then (emitFinalOccurrences_run C store G J k M A circuit firstCount code Bcoef Batom
    bits a hc hG hb hr hJ hk hM hA hcirc hfirst hcode hram hcursor hbits hbound
    hfit hW hindex hB hAtomFit hCoef hCoefFit)
    (fun b ⟨bo,bs,br,bc,bfr⟩ n1 hn1=>?_)
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
  refine ⟨⟨?_,zsrc.trans bs,by rw [zr]; exact br,zc,
    bfr.trans ((dfr.weaken (by decide)).trans
      ((Fr.set _ _ (by decide)).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zo]
    change d.out++_=_
    rw [doo,bo]
    have htoks : toks (sourceFinalWalkFormula G J k M A circuit firstCount code bits)=
      (sourceFinalOccurrenceForms G J k M A circuit firstCount code bits).flatMap toks++
        [.const 0]++List.replicate G .add := by
      simpa only [sourceFinalWalkFormula,sourceFinalOccurrenceForms,List.length_ofFn] using
        (originalSumList_tokens (sourceFinalOccurrenceForms G J k M A circuit firstCount code bits))
    rw [htoks]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.flatMap_assoc,List.append_assoc]
  · have hz : (tokWord (.const 0)).length=9 := by decide
    have ha : (tokWord .add).length=5 := by decide
    rw [hz] at hn2
    rw [ha] at hn4
    nlinarith only [hn1,hn2,hn3,hn4]

end NearQuarticWires.StageCert.Tokens
