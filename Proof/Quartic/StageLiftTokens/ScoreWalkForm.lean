import Proof.Quartic.StageLiftTokens.ScoreOccurrenceLoop
import Proof.Quartic.StageCert.DigitWalkForm

/-!
# The integer score form

`lem:residue` and `lem:print`, paper/paper.tex: the Y form is the original occurrence sum with unit
coefficients on the selected circuit. Its postfix encoding includes
the literal trailing zero and one addition for each occurrence.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageCert.Tokens

def sourceScoreWalkFormula (G circuit firstCount code : ℕ) : Formula (17*G) :=
  Formula.sumList (sourceScoreOccurrenceForms G circuit firstCount code)

def emitScoreWalkForm : St VV MM :=
  .seq emitScoreOccurrences (.seq (StageLift.emitOperator (.const 0))
    (.seq (.op (.copy sourceRecordLimit atomCount)) (emitCopies .add)))

def scoreWalkScratch : List (Fin VV) :=
  atomOccurrence::sourceRecordLimit::sourceRecordIndex::(scoreOccurrenceScratch++StageLift.tokenScratch)

theorem emitScoreWalkForm_run (C : Ctx) (G circuit firstCount code Batom : ℕ)
    (a : DS VV MM) (hc : Cst a) (hb : a.env atomCount=G)
    (hcirc : a.env selectedCircuit=circuit) (hfirst : a.env firstGateCount=firstCount)
    (hcode : a.env newtonTau=code) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd) :
    Hs C emitScoreWalkForm a (G*(8*(40+160*Batom+640)+60)+40) (fun z=>
      z.out=a.out++(toks (sourceScoreWalkFormula G circuit firstCount code)).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z scoreWalkScratch) := by
  have hGfit : G<2^C.Wd := by omega
  unfold emitScoreWalkForm
  apply Hx.hs
  refine Hs.then (emitScoreOccurrences_run C G circuit firstCount code Batom a hc hb
    hcirc hfirst hcode hW hindex hB hAtomFit)
    (fun b ⟨bo,bs,bc,bfr⟩ n1 hn1=>?_)
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
  refine ⟨⟨?_,zs.trans (ds.trans bs),zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans
      ((Fr.set _ _ (by decide)).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zo]
    change d.out++_=_
    rw [doo,bo]
    have htoks : toks (sourceScoreWalkFormula G circuit firstCount code)=
      (sourceScoreOccurrenceForms G circuit firstCount code).flatMap toks++
        [.const 0]++List.replicate G .add := by
      simpa only [sourceScoreWalkFormula,sourceScoreOccurrenceForms,List.length_ofFn] using
        (originalSumList_tokens (sourceScoreOccurrenceForms G circuit firstCount code))
    rw [htoks]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.flatMap_assoc,List.append_assoc]
  · have hz : (tokWord (.const 0)).length=9 := by decide
    have ha : (tokWord .add).length=5 := by decide
    rw [hz] at hn2
    rw [ha] at hn4
    nlinarith only [hn1,hn2,hn3,hn4]

end NearQuarticWires.StageLiftTokens
