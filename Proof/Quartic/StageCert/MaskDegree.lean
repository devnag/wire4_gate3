import Proof.Quartic.StageCert.TupleSum

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: an original mask degree term uses its full signed Newton
coefficient and its complete guarded occurrence-subset polynomial. -/
def emitMaskDegree (store : Fin MM) (edge : Fin 8) : St VV MM :=
  .seq emitNewton (.seq computeTupleTotal
    (.seq (emitTupleElementary store edge) (StageLift.emitOperator .mul)))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: degree-term scratch excludes the original cutoff, degree,
bank size, partition width, and every retained source record. -/
def maskDegreeScratch : List (Fin VV) :=
  newtonScratch++tupleTotal::tupleAddress::checkedTupleScratch

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: one complete original mask
degree term is physically emitted from original source data, with exact
signed arithmetic and the full bounded-subset construction cost. -/
theorem emitMaskDegree_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree tau k B Bn : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (hd : a.env newtonIndex=degree)
    (htau : a.env newtonTau=tau) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^degree≤2^C.Wd) (hwidth : 2*degree+2≤C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd)
    (hBn : natBitLength (Mask.newtonCoeff tau degree).natAbs≤Bn) (hNBit : Bn+2<2^C.Wd) :
    Hs C (emitMaskDegree store edge) a
      (G^degree*(degree*((bits.length+5*(k+G)+160*B+530)+4)+50*degree+200+20)+
        30*degree+40*Bn+400) (fun z=>
      z.out=a.out++(toks (Formula.mul (.const (Mask.newtonCoeff tau degree))
        (tupleElementary (StagePrint.selectedSquare (by decide : 0<4)
          (fun i : Fin G=>bits.getD (k+i.val) false) edge) degree))).flatMap tokWord ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z maskDegreeScratch) := by
  have hp : 0<G^degree := Nat.pow_pos (by omega)
  have hcount : G^degree<2^C.Wd := by omega
  have hdfit : degree<2^C.Wd := (show degree<C.Wd by omega).trans (Nat.lt_two_pow_self)
  unfold emitMaskDegree
  apply Hx.hs
  refine Hs.then (emitNewton_run C a hc tau degree Bn htau hd hwidth (by omega) hBn hNBit)
    (fun b ⟨bo,bs,bc,bfr⟩ n1 hn1=>?_)
  refine Hs.then (computeTupleTotal_run C b bc G degree hG
    ((bfr _ (by decide)).trans hb) ((bfr _ (by decide)).trans hd) hcount hdfit)
    (fun d ⟨dt,ds,dc,dfr⟩ n2 hn2=>?_)
  have df : Fr a d maskDegreeScratch :=
    (bfr.weaken (by decide)).trans (dfr.weaken (by decide))
  have dram : d.ram=a.ram :=
    (congrArg (fun q=>q.2.2.1) ds).trans (congrArg (fun q=>q.2.1) bs)
  have drc : d.rc=a.rc :=
    (congrArg (fun q=>q.2.2.2.1) ds).trans (congrArg (fun q=>q.2.2.1) bs)
  have dsrc : (d.ip,d.ram,d.kin,d.kout,d.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) := by
    simp only [DS.sh,Prod.mk.injEq] at ds
    simp only [Prod.mk.injEq] at bs ⊢
    exact ⟨ds.1.trans bs.1,ds.2.2.1.trans bs.2.1,
      ds.2.2.2.2.1.trans bs.2.2.2.1,ds.2.2.2.2.2.1.trans bs.2.2.2.2.1,
      ds.2.2.2.2.2.2.trans bs.2.2.2.2.2⟩
  have dout : d.out=b.out := congrArg (fun q=>q.2.1) ds
  refine Hs.then (emitTupleElementary_run C store edge G degree k B bits d dc hG
    ((df _ (by decide)).trans hb) dt ((df _ (by decide)).trans hd)
    ((df _ (by decide)).trans hk) (by rw [dram]; exact hram) (by rw [drc]; exact hcursor)
    hbits haddress hfit hdfit hW hindex hB hBit)
    (fun q ⟨qo,qs,qr,qc,qfr⟩ n3 hn3=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .mul q qc)
    (fun z ⟨zo,zs,zc,zfr⟩ n4 hn4=>?_)
  have zr : z.rc=q.rc := congrArg (fun q=>q.2.2.1) zs
  have zsrc : (z.ip,z.ram,z.kin,z.kout,z.kc)=(q.ip,q.ram,q.kin,q.kout,q.kc) := by
    simp only [Prod.mk.injEq] at zs ⊢
    exact ⟨zs.1,zs.2.1,zs.2.2.2.1,zs.2.2.2.2.1,zs.2.2.2.2.2⟩
  refine ⟨⟨?_,zsrc.trans (qs.trans dsrc),by rw [zr]; exact qr,zc,
    df.trans ((qfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩,?_⟩
  · rw [zo,qo,dout,bo]
    simp only [toks,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  · have hm : (tokWord .mul).length=7 := by decide
    rw [hm] at hn4
    omega

end NearQuarticWires.StageCert.Tokens
