import Proof.Quartic.StageCert.PopulationSource

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testX` and `lem:print`, paper/paper.tex: close the physically read selected-square list by its
literal zero and exactly one addition per original occurrence. -/
def emitPopulationForm (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq (emitPopulationSquares store edge) (.seq (StageLift.emitOperator (.const 0))
    (.seq (.op (.copy sourceRecordLimit atomCount)) (emitCopies .add)))

/-- `eq:testX`, `lem:print` and `prop:time`, paper/paper.tex: the original complete
population AST is physically emitted from actual retained selection bits,
without a supplied active-label set or a passing-column premise. -/
theorem emitPopulationForm_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G k B : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hb : a.env atomCount=G) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hfit : B+2<2^C.Wd) :
    Hs C (emitPopulationForm store edge) a
      (G*(bits.length+5*(k+G)+160*B+540)+40) (fun z=>
      z.out=a.out++(toks (StagePrint.selectedPopulationFormula (by decide : 0<4)
        (fun i : Fin G=>bits.getD (k+i.val) false) edge)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (atomOccurrence::populationSourceScratch)) := by
  have hGfit : G<2^C.Wd := by omega
  unfold emitPopulationForm
  apply Hx.hs
  refine Hs.then (emitPopulationSquares_run C store edge G k B bits a hc hG hb hk
    hram hcursor hbits haddress hW hindex hB hfit)
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
    rw [StagePrint.selectedPopulationFormula,originalSumList_tokens]
    simp only [List.length_ofFn,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.flatMap_assoc,List.append_assoc]
  · have hz : (tokWord (.const 0)).length=9 := by decide
    have ha : (tokWord .add).length=5 := by decide
    rw [hz] at hn2
    rw [ha] at hn4
    nlinarith only [hn1,hn2,hn3,hn4]

end NearQuarticWires.StageCert.Tokens
