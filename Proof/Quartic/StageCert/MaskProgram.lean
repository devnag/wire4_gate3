import Proof.Quartic.StageCert.MaskSumLoop

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `def:mask` and `lem:print`, paper/paper.tex: the actual center-independent structural bit of one edge. -/
def maskStructural : Fin VV := ⟨123,by decide⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: serialize the actual structural bit, complete signed
Newton sum, and original outer multiplication in the literal integer codec. -/
def emitMask (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq (StageLift.emitNaturalConstant maskStructural)
    (.seq (emitMaskDegrees store edge)
      (.seq (StageLift.emitOperator (.const 0))
        (.seq (.op (.copy sourceRecordLimit maskLimit))
          (.seq (emitCopies .add) (StageLift.emitOperator .mul)))))

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the complete original integer
mask is physically produced from actual bank/witness fields. Every degree,
bounded tuple, invalid zero coefficient and signed Newton constant is paid;
the result agrees with the original mask on every bad column as well. -/
theorem emitMask_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G tau Xmax k B Bn : ℕ) (bits : List Bool) (structural : Bool)
    (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (htau : a.env newtonTau=tau)
    (hlimit : a.env maskLimit=Xmax+1) (hk : a.env selectionStart=k)
    (hstruct : a.env maskStructural=structural.toNat)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^Xmax≤2^C.Wd) (hwidth : 2*Xmax+2≤C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd)
    (hBn : ∀ degree≤Xmax,natBitLength (Mask.newtonCoeff tau degree).natAbs≤Bn)
    (hNBit : Bn+2<2^C.Wd) :
    Hs C (emitMask store edge) a
      ((Xmax+1)*((G^Xmax*(Xmax*((bits.length+5*(k+G)+160*B+530)+4)+50*Xmax+200+20)+
        30*Xmax+40*Bn+400)+20)+200) (fun z=>
      z.out=a.out++(toks (tupleMaskFormula structural
        (StagePrint.selectedSquare (by decide : 0<4) (fun i : Fin G=>bits.getD (k+i.val) false) edge)
        tau Xmax)).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (newtonIndex::maskDegreeScratch)) := by
  have h32 : 32≤2^C.Wd := by
    have hh := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at hh
    exact hh
  have hsbits : natBitLength (a.env maskStructural)≤1 := by
    rw [hstruct]
    cases structural <;> norm_num [natBitLength]
  have hcount : Xmax+1<2^C.Wd := (show Xmax+1<C.Wd by omega).trans Nat.lt_two_pow_self
  have erase {b d : DS VV MM}
      (h : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(d.ip,d.ram,d.rc,d.kin,d.kout,d.kc)) :
      (b.ip,b.ram,b.kin,b.kout,b.kc)=(d.ip,d.ram,d.kin,d.kout,d.kc) := by
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2⟩
  unfold emitMask
  apply Hx.hs
  refine Hs.then ((StageLift.emitNaturalConstant_spec C maskStructural (by decide) (by decide)
    a hc (by omega) (by omega)).mono (t' := 96) (by omega) (fun _ h=>h))
    (fun b ⟨bo,bs,bc,bfr⟩ n1 hn1=>?_)
  have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
  have brc : b.rc=a.rc := congrArg (fun q=>q.2.2.1) bs
  refine Hs.then (emitMaskDegrees_run C store edge G tau Xmax k B Bn bits b bc hG
    ((bfr _ (by decide)).trans hb) ((bfr _ (by decide)).trans htau)
    ((bfr _ (by decide)).trans hlimit) ((bfr _ (by decide)).trans hk)
    (by rw [bram]; exact hram) (by rw [brc]; exact hcursor) hbits haddress hfit hwidth
    hW hindex hB hBit hBn hNBit)
    (fun d ⟨doo,ds,dr,dc,dfr⟩ n2 hn2=>?_)
  refine Hs.then (StageLift.emitOperator_spec C (.const 0) d dc)
    (fun e ⟨eo,es,ec,efr⟩ n3 hn3=>?_)
  refine Hs.then (hs_copy C sourceRecordLimit maskLimit e (by decide))
    (fun f hf n4 hn4=>?_)
  subst hf
  let f := e.set sourceRecordLimit (e.env maskLimit)
  have el : e.env maskLimit=Xmax+1 :=
    (efr _ (by decide)).trans ((dfr _ (by decide)).trans ((bfr _ (by decide)).trans hlimit))
  have fc : Cst f := Cst.of_fr (T := [sourceRecordLimit]) ec (Fr.set _ _ (by simp)) (by decide)
  have fl : f.env sourceRecordLimit=Xmax+1 := by
    change e.env maskLimit=Xmax+1
    exact el
  refine Hs.then (emitCopies_run C .add f fc (Xmax+1) fl hcount)
    (fun q ⟨qo,qs,qc,qfr⟩ n5 hn5=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .mul q qc)
    (fun z ⟨zo,zs,zc,zfr⟩ n6 hn6=>?_)
  have zr : z.rc=d.rc := (congrArg (fun x=>x.2.2.1) zs).trans
    ((congrArg (fun x=>x.2.2.1) qs).trans (congrArg (fun x=>x.2.2.1) es))
  refine ⟨⟨?_,(erase zs).trans ((erase qs).trans ((erase es).trans (ds.trans (erase bs)))),
    by rw [zr]; exact dr,zc,
    (bfr.weaken (by decide)).trans (dfr.trans ((efr.weaken (by decide)).trans
      ((Fr.set _ _ (by simp [maskDegreeScratch,checkedTupleScratch,tupleFactorScratch])).trans
        ((qfr.weaken (by decide)).trans (zfr.weaken (by decide))))))⟩,?_⟩
  · rw [zo,qo]
    change e.out++_++_=_
    rw [eo,doo,bo,hstruct]
    cases structural <;>
      simp only [Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,Nat.cast_one,
        tupleMaskFormula,toks,formulaListSum_tokens,selectedMaskDegrees,List.length_ofFn,
        List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,
        List.flatMap_assoc,Bool.false_eq_true,if_false,if_true]
  · have hz : (tokWord (.const 0)).length=9 := by decide
    have ha : (tokWord .add).length=5 := by decide
    have hm : (tokWord .mul).length=7 := by decide
    rw [hz] at hn3
    rw [ha] at hn5
    rw [hm] at hn6
    nlinarith only [hn1,hn2,hn3,hn4,hn5,hn6]

end NearQuarticWires.StageCert.Tokens
