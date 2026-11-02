import Proof.Quartic.StageCert.MaskProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:print`(b), paper/paper.tex: all original
edge-mask formulas share the same seventeen-role occurrence pool. -/
def selectedWalkMasks (G tau k Xmax : ℕ) (bits : List Bool)
    (structural : Fin 8→Bool) (edges : List (Fin 8)) : List (Formula (17*G)) :=
  edges.map (fun edge=>tupleMaskFormula (structural edge)
    (StagePrint.selectedSquare (by decide : 0<4) (fun i : Fin G=>bits.getD (k+i.val) false) edge)
    tau Xmax)

/-- `lem:print`(b), paper/paper.tex: read each actual
structural source bit, emit its complete integer mask, and close the
literal product of the fixed original walk edges. -/
def emitWalkMaskProduct (store : Fin MM) : List (Fin 8)→St VV MM
  | [] => StageLift.emitOperator (.const 1)
  | edge::edges => .seq (.op (.rdI maskStructural))
      (.seq (emitMask store edge)
        (.seq (emitWalkMaskProduct store edges) (StageLift.emitOperator .mul)))

/-- `prop:time`, paper/paper.tex: fixed-edge mask
composition adds its source read, complete mask, remaining masks and
literal multiplication costs, without changing the source exponent. -/
theorem walkMaskCostStep (length M n1 n2 n3 n4 : ℕ)
    (h1 : n1≤1) (h2 : n2≤M) (h3 : n3≤length*(M+20)+20) (h4 : n4≤15) :
    n1+(n2+(n3+n4+1)+1)+1≤(length+1)*(M+20)+20 := by
  rw [Nat.add_mul,Nat.one_mul]
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: all fixed walk masks are physically serialized with their
literal source structural bits. This program never evaluates centers or
assumes a passing certification test. -/
theorem emitWalkMaskProduct_run (C : Ctx) (store : Fin MM)
    (G tau Xmax k B Bn : ℕ) (bits : List Bool) (structural : Fin 8→Bool)
    (edges : List (Fin 8)) (rest : List Bool) (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hin : C.inp.drop a.ip=edges.map structural++rest)
    (hb : a.env atomCount=G) (htau : a.env newtonTau=tau)
    (hlimit : a.env maskLimit=Xmax+1) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^Xmax≤2^C.Wd) (hwidth : 2*Xmax+2≤C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd)
    (hBn : ∀ degree≤Xmax,natBitLength (Mask.newtonCoeff tau degree).natAbs≤Bn)
    (hNBit : Bn+2<2^C.Wd) :
    Hs C (emitWalkMaskProduct store edges) a
      (edges.length*(((Xmax+1)*((G^Xmax*(Xmax*((bits.length+5*(k+G)+160*B+530)+4)+50*Xmax+200+20)+
        30*Xmax+40*Bn+400)+20)+200)+20)+20) (fun z=>
      z.out=a.out++(toks (Mask.formulaListProd
        (selectedWalkMasks G tau k Xmax bits structural edges))).flatMap tokWord ∧
      z.ip=a.ip+edges.length ∧ (z.ram,z.kin,z.kout,z.kc)=(a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (maskStructural::newtonIndex::maskDegreeScratch)) := by
  induction edges generalizing a with
  | nil =>
    refine (StageLift.emitOperator_spec C (.const 1) a hc).mono
      (by
        have hh : (tokWord (.const 1)).length=9 := by decide
        rw [hh]
        simp) ?_
    rintro z ⟨zo,zs,zc,zfr⟩
    simp only [Prod.mk.injEq] at zs
    exact ⟨by simpa [selectedWalkMasks,Mask.formulaListProd,toks] using zo,
      by simpa using zs.1,
      (by simp only [Prod.mk.injEq]; exact ⟨zs.2.1,zs.2.2.2.1,zs.2.2.2.2.1,zs.2.2.2.2.2⟩),
      by rw [zs.2.2.1]; exact hcursor,zc,zfr.weaken (by decide)⟩
  | cons edge edges ih =>
    have hpos : a.ip<C.inp.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hin
      simp at hin
    have hread : bitOf C.inp a.ip=(structural edge).toNat := by
      simpa using bitOf_drop hin 0 (by simp)
    unfold emitWalkMaskProduct
    apply Hx.hs
    refine Hs.then (hs_rdI C maskStructural a hpos) (fun b hbe n1 hn1=>?_)
    subst hbe
    let b : DS VV MM := { a.set maskStructural (bitOf C.inp a.ip) with ip:=a.ip+1 }
    have bfr : Fr a b [maskStructural] := Fr.set _ _ (by simp)
    have bc : Cst b := Cst.of_fr hc bfr (by decide)
    refine Hs.then (emitMask_run C store edge G tau Xmax k B Bn bits (structural edge) b bc hG
      ((bfr _ (by decide)).trans hb) ((bfr _ (by decide)).trans htau)
      ((bfr _ (by decide)).trans hlimit) ((bfr _ (by decide)).trans hk)
      (by change bitOf C.inp a.ip=(structural edge).toNat; exact hread)
      hram hcursor hbits haddress hfit hwidth hW hindex (fun g hg j=>hB g hg edge j) hBit hBn hNBit)
      (fun d ⟨doo,ds,dr,dc,dfr⟩ n2 hn2=>?_)
    have dip : d.ip=a.ip+1 := congrArg Prod.fst ds
    have dinput : C.inp.drop d.ip=edges.map structural++rest := by
      rw [dip,←List.drop_drop,hin]
      simp
    have dram : d.ram=a.ram := congrArg (fun q=>q.2.1) ds
    have df : Fr a d (maskStructural::newtonIndex::maskDegreeScratch) :=
      (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
    refine Hs.then (ih d dc dinput ((df _ (by decide)).trans hb)
      ((df _ (by decide)).trans htau) ((df _ (by decide)).trans hlimit)
      ((df _ (by decide)).trans hk) (by rw [dram]; exact hram) dr)
      (fun q ⟨qo,qi,qs,qr,qc,qfr⟩ n3 hn3=>?_)
    refine Hs.last (StageLift.emitOperator_spec C .mul q qc)
      (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
    have zrc : z.rc=q.rc := congrArg (fun x=>x.2.2.1) zs
    have zip : z.ip=q.ip := congrArg Prod.fst zs
    have zsmall : (z.ram,z.kin,z.kout,z.kc)=(q.ram,q.kin,q.kout,q.kc) := by
      simp only [Prod.mk.injEq] at zs ⊢
      exact ⟨zs.2.1,zs.2.2.2.1,zs.2.2.2.2.1,zs.2.2.2.2.2⟩
    have dsmall : (d.ram,d.kin,d.kout,d.kc)=(a.ram,a.kin,a.kout,a.kc) := by
      exact congrArg Prod.snd ds
    refine ⟨⟨?_,by rw [zip,qi,dip]; simp; omega,zsmall.trans (qs.trans dsmall),
      by rw [zrc]; exact qr,zc,df.trans (qfr.trans (zfr.weaken (by decide)))⟩,?_⟩
    · rw [zo,qo,doo]
      change a.out++_++_++_=_
      simp only [selectedWalkMasks,List.map_cons,Mask.formulaListProd,toks,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
    · have hm : (tokWord .mul).length=7 := by decide
      rw [hm] at hn4
      exact walkMaskCostStep edges.length _ n1 n2 n3 n4 hn1 hn2 hn3 hn4

end NearQuarticWires.StageCert.Tokens
