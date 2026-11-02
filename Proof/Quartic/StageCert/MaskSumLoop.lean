import Proof.Quartic.StageCert.MaskDegree

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual number `Xmax+1` of original Newton terms. -/
def maskLimit : Fin VV := ⟨120,by decide⟩

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: original mask degree terms in their physical increasing
degree order, with exact signed coefficients. -/
def selectedMaskDegrees (G tau k Xmax : ℕ) (bits : List Bool) (edge : Fin 8) : List (Formula (17*G)) :=
  List.ofFn (fun degree : Fin (Xmax+1)=>Formula.mul (.const (Mask.newtonCoeff tau degree.val))
    (tupleElementary (StagePrint.selectedSquare (by decide : 0<4)
      (fun i : Fin G=>bits.getD (k+i.val) false) edge) degree.val))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: every original Newton term is computed and emitted by a
real dynamic-degree loop on the unchanged seventeen-role occurrence pool. -/
def emitMaskDegrees (store : Fin MM) (edge : Fin 8) : St VV MM :=
  forS newtonIndex maskLimit (emitMaskDegree store edge)

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: complete mask degree terms
are physically serialized with the full bounded-subset construction count;
all signed original coefficients and all bad columns are retained. -/
theorem emitMaskDegrees_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G tau Xmax k B Bn : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (htau : a.env newtonTau=tau)
    (hlimit : a.env maskLimit=Xmax+1) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^Xmax≤2^C.Wd) (hwidth : 2*Xmax+2≤C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd)
    (hBn : ∀ degree≤Xmax,natBitLength (Mask.newtonCoeff tau degree).natAbs≤Bn)
    (hNBit : Bn+2<2^C.Wd) :
    Hs C (emitMaskDegrees store edge) a
      ((Xmax+1)*((G^Xmax*(Xmax*((bits.length+5*(k+G)+160*B+530)+4)+50*Xmax+200+20)+
        30*Xmax+40*Bn+400)+4)+4) (fun z=>
      z.out=a.out++(selectedMaskDegrees G tau k Xmax bits edge).flatMap
        (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (newtonIndex::maskDegreeScratch)) := by
  let fs := selectedMaskDegrees G tau k Xmax bits edge
  let I : ℕ→DS VV MM→Prop := fun i b=>b.out=a.out++factorPrefix fs i ∧
    (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
    b.rc store≤bits.length ∧ Cst b ∧ Fr a b (newtonIndex::maskDegreeScratch)
  have hset : ∀ i b v,I i b→I i (b.set newtonIndex v) := by
    rintro i b v ⟨bo,bs,br,bc,bf⟩
    exact ⟨bo,bs,br,Cst.of_fr (T := [newtonIndex]) bc (Fr.set _ _ (by simp)) (by decide),
      bf.trans (Fr.set _ _ (by simp))⟩
  have hcount : Xmax+1<2^C.Wd := (show Xmax+1<C.Wd by omega).trans Nat.lt_two_pow_self
  unfold emitMaskDegrees
  refine (forS_spec' (C := C) newtonIndex maskLimit (by decide) (emitMaskDegree store edge) a
    (Xmax+1) hcount I
    (G^Xmax*(Xmax*((bits.length+5*(k+G)+160*B+530)+4)+50*Xmax+200+20)+
      30*Xmax+40*Bn+400) hset ⟨by simp [factorPrefix],rfl,hcursor,hc,Fr.refl _ _⟩ hlimit ?_).mono le_rfl ?_
  · intro degree hi b ⟨bo,bs,br,bc,bfr⟩ bi bn
    have hdeg : degree≤Xmax := by omega
    have hp : G^degree≤G^Xmax := Nat.pow_le_pow_right hG hdeg
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
    refine (emitMaskDegree_run C store edge G degree tau k B Bn bits b bc hG
      ((bfr _ (by decide)).trans hb) bi ((bfr _ (by decide)).trans htau)
      ((bfr _ (by decide)).trans hk) (by rw [bram]; exact hram) br hbits haddress
      (by omega) (by omega) hW hindex hB hBit (hBn degree hdeg) hNBit).mono ?_ ?_
    · have hlin : degree*((bits.length+5*(k+G)+160*B+530)+4)+50*degree+200+20≤
          Xmax*((bits.length+5*(k+G)+160*B+530)+4)+50*Xmax+200+20 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add (Nat.mul_le_mul_right _ hdeg) (Nat.mul_le_mul_left _ hdeg)) _) _
      have hm := Nat.mul_le_mul hp hlin
      exact Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add hm (Nat.mul_le_mul_left _ hdeg)) _) _
    · rintro z ⟨zo,zs,zr,zc,zfr⟩
      have hil : degree<fs.length := by simpa [fs,selectedMaskDegrees] using hi
      have zform : z.out=b.out++(toks fs[degree]).flatMap tokWord := by
        simpa only [fs,selectedMaskDegrees,List.getElem_ofFn] using zo
      refine ⟨⟨?_,zs.trans bs,zr,zc,
        bfr.trans (zfr.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx))⟩,?_,?_⟩
      · rw [zform,bo]
        simp only [factorPrefix,List.take_succ_eq_append_getElem hil,List.flatMap_append,
          List.flatMap_singleton,List.append_assoc]
      · rw [zfr _ (by decide)]
        exact bi
      · rw [zfr _ (by decide)]
        exact bn
  · rintro z ⟨⟨zo,zs,zr,zc,zfr⟩,_,_⟩
    refine ⟨?_,zs,zr,zc,zfr⟩
    have htake : fs.take (Xmax+1)=fs := List.take_of_length_le (by simp [fs,selectedMaskDegrees])
    simpa only [factorPrefix,htake] using zo

end NearQuarticWires.StageCert.Tokens
