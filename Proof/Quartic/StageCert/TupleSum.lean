import Proof.Quartic.StageCert.TupleSumLoop

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the guarded tuple list is closed by a literal zero and
exactly `G^a` original addition tokens. -/
def emitTupleElementary (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq (emitTupleTerms store edge)
    (.seq (StageLift.emitOperator (.const 0))
      (.seq (.op (.copy sourceRecordLimit tupleTotal)) (emitCopies .add)))

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the complete original
elementary-symmetric subset polynomial is physically serialized from
bounded addresses and original witness records, including every zero term. -/
theorem emitTupleElementary_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree k B : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (ht : a.env tupleTotal=G^degree)
    (hd : a.env newtonIndex=degree) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^degree≤2^C.Wd) (hdfit : degree<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd) :
    Hs C (emitTupleElementary store edge) a
      (G^degree*(degree*((bits.length+5*(k+G)+160*B+530)+4)+50*degree+200+20)+50)
      (fun z=>z.out=a.out++(toks (tupleElementary
        (StagePrint.selectedSquare (by decide : 0<4) (fun i : Fin G=>bits.getD (k+i.val) false) edge)
        degree)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (tupleAddress::checkedTupleScratch)) := by
  have hcount : G^degree<2^C.Wd := by
    have hp : 0<G^degree := Nat.pow_pos (by omega)
    omega
  unfold emitTupleElementary
  apply Hx.hs
  refine Hs.then (emitTupleTerms_run C store edge G degree k B bits a hc hG hb ht hd hk
    hram hcursor hbits haddress hfit hdfit hW hindex hB hBit)
    (fun b ⟨bo,bs,br,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (StageLift.emitOperator_spec C (.const 0) b bc)
    (fun d ⟨doo,ds,dc,dfr⟩ n2 hn2=>?_)
  refine Hs.then (hs_copy C sourceRecordLimit tupleTotal d (by decide))
    (fun e he n3 hn3=>?_)
  subst he
  let e := d.set sourceRecordLimit (d.env tupleTotal)
  have dr : d.rc=b.rc := congrArg (fun q=>q.2.2.1) ds
  have dsrc : (d.ip,d.ram,d.kin,d.kout,d.kc)=(b.ip,b.ram,b.kin,b.kout,b.kc) := by
    simp only [Prod.mk.injEq] at ds ⊢
    exact ⟨ds.1,ds.2.1,ds.2.2.2.1,ds.2.2.2.2.1,ds.2.2.2.2.2⟩
  have dt : d.env tupleTotal=G^degree := (dfr _ (by decide)).trans ((bfr _ (by decide)).trans ht)
  have ec : Cst e := Cst.of_fr (T := [sourceRecordLimit]) dc (Fr.set _ _ (by simp)) (by decide)
  have et : e.env sourceRecordLimit=G^degree := by
    change d.env tupleTotal=G^degree
    exact dt
  refine Hs.last (emitCopies_run C .add e ec (G^degree) et hcount)
    (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
  have zr : z.rc=d.rc := congrArg (fun q=>q.2.2.1) zs
  have zsrc : (z.ip,z.ram,z.kin,z.kout,z.kc)=(d.ip,d.ram,d.kin,d.kout,d.kc) := by
    simp only [Prod.mk.injEq] at zs ⊢
    exact ⟨zs.1,zs.2.1,zs.2.2.2.1,zs.2.2.2.2.1,zs.2.2.2.2.2⟩
  refine ⟨⟨?_,zsrc.trans (dsrc.trans bs),by rw [zr,dr]; exact br,zc,
    bfr.trans ((dfr.weaken (by decide)).trans
      ((Fr.set _ _ (by simp [checkedTupleScratch,tupleFactorScratch])).trans (zfr.weaken (by decide))))⟩,?_⟩
  · rw [zo]
    change d.out++_=_
    rw [doo,bo]
    simp only [tupleElementary,formulaListSum_tokens,selectedTupleTerms,List.length_ofFn,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,
      List.flatMap_assoc]
  · have hh : (tokWord (.const 0)).length=9 := by decide
    have ha : (tokWord .add).length=5 := by decide
    rw [hh] at hn2
    rw [ha] at hn4
    nlinarith only [hn1,hn2,hn3,hn4]

end NearQuarticWires.StageCert.Tokens
