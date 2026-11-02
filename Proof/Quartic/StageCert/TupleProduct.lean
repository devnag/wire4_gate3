import Proof.Quartic.StageCert.TupleFactorLoop
import Proof.Quartic.StageCert.FoldTokens

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: after the actual factor stream, one unit and exactly the
original degree's multiplication tokens close the literal product. -/
def emitTupleProduct (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq (emitTupleFactors store edge)
    (.seq (StageLift.emitOperator (.const 1))
      (.seq (.op (.copy sourceRecordLimit newtonIndex)) (emitCopies .mul)))

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the full tuple product is
physically serialized from original witness records, retaining exact
integer syntax even on bad columns and unselected occurrences. -/
theorem emitTupleProduct_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree k B : ℕ) (address : Fin (G^degree)) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (hp : a.env tuplePower=G^degree)
    (ha : a.env tupleAddress=address.val) (hd : a.env newtonIndex=degree)
    (hk : a.env selectionStart=k) (hram : a.ram store=bits.map Bool.toNat)
    (hcursor : a.rc store≤bits.length) (hbits : k+G≤bits.length)
    (haddress : k+G≤2^C.Wd) (hfit : 2*G^degree≤2^C.Wd) (hdfit : degree<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd) :
    Hs C (emitTupleProduct store edge) a
      (degree*((bits.length+5*(k+G)+160*B+530)+4)+20*degree+50) (fun z=>
      z.out=a.out++(toks (Mask.formulaListProd
        (selectedTupleFactors G degree k bits edge address))).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (tuplePosition::tupleFactorScratch)) := by
  unfold emitTupleProduct
  apply Hx.hs
  refine Hs.then (emitTupleFactors_run C store edge G degree k B address bits a hc hG hb hp ha hd
    hk hram hcursor hbits haddress hfit hdfit hW hindex hB hBit)
    (fun b ⟨bo,bs,br,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (StageLift.emitOperator_spec C (.const 1) b bc)
    (fun d ⟨doo,ds,dc,dfr⟩ n2 hn2=>?_)
  refine Hs.then (hs_copy C sourceRecordLimit newtonIndex d (by decide))
    (fun e he n3 hn3=>?_)
  subst he
  let e := d.set sourceRecordLimit (d.env newtonIndex)
  have dr : d.rc=b.rc := congrArg (fun q=>q.2.2.1) ds
  have dsrc : (d.ip,d.ram,d.kin,d.kout,d.kc)=(b.ip,b.ram,b.kin,b.kout,b.kc) := by
    simp only [Prod.mk.injEq] at ds ⊢
    exact ⟨ds.1,ds.2.1,ds.2.2.2.1,ds.2.2.2.2.1,ds.2.2.2.2.2⟩
  have dd : d.env newtonIndex=degree := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans hd)
  have ec : Cst e := Cst.of_fr (T := [sourceRecordLimit]) dc (Fr.set _ _ (by simp)) (by decide)
  have ecount : e.env sourceRecordLimit=degree := by
    change d.env newtonIndex=degree
    exact dd
  refine Hs.last (emitCopies_run C .mul e ec degree ecount hdfit)
    (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
  have zr : z.rc=d.rc := congrArg (fun q=>q.2.2.1) zs
  have zsrc : (z.ip,z.ram,z.kin,z.kout,z.kc)=(d.ip,d.ram,d.kin,d.kout,d.kc) := by
    simp only [Prod.mk.injEq] at zs ⊢
    exact ⟨zs.1,zs.2.1,zs.2.2.2.1,zs.2.2.2.2.1,zs.2.2.2.2.2⟩
  refine ⟨⟨?_,zsrc.trans (dsrc.trans bs),by rw [zr,dr]; exact br,zc,
    bfr.trans ((dfr.weaken (by decide)).trans
      ((Fr.set _ _ (by simp [tupleFactorScratch])).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zo]
    change d.out++_=_
    rw [doo,bo,formulaListProd_tokens]
    simp only [selectedTupleFactors,List.length_ofFn,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc,List.flatMap_assoc]
  · have hh : (tokWord (.const 1)).length=9 := by decide
    have hm : (tokWord .mul).length=7 := by decide
    rw [hh] at hn2
    rw [hm] at hn4
    omega

end NearQuarticWires.StageCert.Tokens
