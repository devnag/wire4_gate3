import Proof.Quartic.StageCert.TuplePrepare

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual tuple guard is computed, emitted, and multiplied
by the original witness-selected product on the same occurrence pool. -/
def emitCheckedTuple (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq prepareTupleOrder (.seq scanTupleOrder
    (.seq (StageLift.emitNaturalConstant tupleOrdered)
      (.seq (.op (.copy tuplePower tupleTotal))
        (.seq (emitTupleProduct store edge) (StageLift.emitOperator .mul)))))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: complete tuple emission retains all source data and changes
only its arithmetic, record scan and literal-token scratch variables. -/
def checkedTupleScratch : List (Fin VV) :=
  tuplePrevious::tupleOrdered::tuplePosition::tupleFactorScratch

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: each complete guarded subset
term is physically produced from original radix/witness data, with exact
zero coefficients on every repeated or unordered tuple. -/
theorem emitCheckedTuple_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree k B : ℕ) (address : Fin (G^degree)) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (ht : a.env tupleTotal=G^degree)
    (ha : a.env tupleAddress=address.val) (hd : a.env newtonIndex=degree)
    (hk : a.env selectionStart=k) (hram : a.ram store=bits.map Bool.toNat)
    (hcursor : a.rc store≤bits.length) (hbits : k+G≤bits.length)
    (haddress : k+G≤2^C.Wd) (hfit : 2*G^degree≤2^C.Wd) (hdfit : degree<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd) :
    Hs C (emitCheckedTuple store edge) a
      (degree*((bits.length+5*(k+G)+160*B+530)+4)+50*degree+200) (fun z=>
      z.out=a.out++(toks (tupleTerm
        (StagePrint.selectedSquare (by decide : 0<4) (fun i : Fin G=>bits.getD (k+i.val) false) edge)
        (tupleAddressEquiv G degree address))).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z checkedTupleScratch) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  have erase {b d : DS VV MM}
      (h : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(d.ip,d.ram,d.rc,d.kin,d.kout,d.kc)) :
      (b.ip,b.ram,b.kin,b.kout,b.kc)=(d.ip,d.ram,d.kin,d.kout,d.kc) := by
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  unfold emitCheckedTuple
  apply Hx.hs
  refine Hs.then (prepareTupleOrder_run C a hc (G^degree) ht)
    (fun b ⟨bp,bo,bs,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (scanTupleOrder_run C b bc G degree address.val hG
    ((bfr _ (by decide)).trans hb) bp ((bfr _ (by decide)).trans ha)
    ((bfr _ (by decide)).trans hd) bo hfit hdfit)
    (fun d ⟨doFlag,ds,dc,dfr⟩ n2 hn2=>?_)
  have dsh : d.sh=a.sh := ds.trans bs
  have df : Fr a d checkedTupleScratch :=
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
  have dh : natBitLength (d.env tupleOrdered)≤1 := by
    rw [doFlag,tupleAddress_orderBit]
    by_cases hp : StrictMono (tupleAddressEquiv G degree address) <;> simp [hp,natBitLength]
  have dz : (d.env tupleOrdered : ℤ)=
      if StrictMono (tupleAddressEquiv G degree address) then 1 else 0 := by
    rw [doFlag,tupleAddress_orderBit]
    by_cases hp : StrictMono (tupleAddressEquiv G degree address) <;> simp [hp]
  refine Hs.then ((StageLift.emitNaturalConstant_spec C tupleOrdered (by decide) (by decide)
    d dc (by omega) (by omega)).mono (t' := 96) (by omega) (fun _ h=>h))
    (fun e ⟨eo,es,ec,efr⟩ n3 hn3=>?_)
  have ef : Fr a e checkedTupleScratch := df.trans (efr.weaken (by decide))
  refine Hs.then (hs_copy C tuplePower tupleTotal e (by decide))
    (fun f hf n4 hn4=>?_)
  subst hf
  let f := e.set tuplePower (e.env tupleTotal)
  have ff : Fr a f checkedTupleScratch := ef.trans (Fr.set _ _ (by simp [checkedTupleScratch,tupleFactorScratch]))
  have fc : Cst f := Cst.of_fr (T := [tuplePower]) ec (Fr.set _ _ (by simp)) (by decide)
  have fp : f.env tuplePower=G^degree := by
    change e.env tupleTotal=G^degree
    exact (ef _ (by decide)).trans ht
  have dsrc : (d.ip,d.ram,d.rc,d.kin,d.kout,d.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at dsh
    simp only [Prod.mk.injEq]
    exact ⟨dsh.1,dsh.2.2.1,dsh.2.2.2.1,dsh.2.2.2.2.1,dsh.2.2.2.2.2.1,dsh.2.2.2.2.2.2⟩
  have fsrc : (f.ip,f.ram,f.rc,f.kin,f.kout,f.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := es.trans dsrc
  have fram : f.ram=a.ram := congrArg (fun q=>q.2.1) fsrc
  have frc : f.rc=a.rc := congrArg (fun q=>q.2.2.1) fsrc
  refine Hs.then (emitTupleProduct_run C store edge G degree k B address bits f fc hG
    ((ff _ (by decide)).trans hb) fp ((ff _ (by decide)).trans ha)
    ((ff _ (by decide)).trans hd) ((ff _ (by decide)).trans hk)
    (by rw [fram]; exact hram) (by rw [frc]; exact hcursor) hbits haddress hfit hdfit
    hW hindex hB hBit)
    (fun q ⟨qo,qs,qr,qc,qfr⟩ n5 hn5=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .mul q qc)
    (fun z ⟨zo,zs,zc,zfr⟩ n6 hn6=>?_)
  have zrc : z.rc=q.rc := congrArg (fun x=>x.2.2.1) zs
  have dout : d.out=a.out := congrArg (fun x=>x.2.1) dsh
  refine ⟨⟨?_,(erase zs).trans (qs.trans (erase fsrc)),by rw [zrc]; exact qr,zc,
    ff.trans ((qfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  · rw [zo,qo]
    change e.out++_++_=_
    rw [eo,dout,dz]
    simp only [tupleTerm,selectedTupleFactors,toks,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]
  · have hm : (tokWord .mul).length=7 := by decide
    rw [hm] at hn6
    omega

end NearQuarticWires.StageCert.Tokens
