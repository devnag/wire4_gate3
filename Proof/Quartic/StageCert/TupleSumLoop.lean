import Proof.Quartic.StageCert.TupleTermProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: the actual list of guarded tuples in exact radix order. -/
def selectedTupleTerms (G degree k : ℕ) (bits : List Bool) (edge : Fin 8) : List (Formula (17*G)) :=
  List.ofFn (fun address : Fin (G^degree)=>tupleTerm
    (StagePrint.selectedSquare (by decide : 0<4) (fun i : Fin G=>bits.getD (k+i.val) false) edge)
    (tupleAddressEquiv G degree address))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: enumerate every actual bounded tuple address, without
enumerating the full original occurrence powerset. -/
def emitTupleTerms (store : Fin MM) (edge : Fin 8) : St VV MM :=
  forS tupleAddress tupleTotal (emitCheckedTuple store edge)

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the actual bounded tuple term
list is serialized exactly from original bank and witness data, retaining
zero invalid tuples and charging its full `G^a` construction count. -/
theorem emitTupleTerms_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree k B : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (ht : a.env tupleTotal=G^degree)
    (hd : a.env newtonIndex=degree) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hfit : 2*G^degree≤2^C.Wd) (hdfit : degree<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd) :
    Hs C (emitTupleTerms store edge) a
      (G^degree*((degree*((bits.length+5*(k+G)+160*B+530)+4)+50*degree+200)+4)+4)
      (fun z=>z.out=a.out++(selectedTupleTerms G degree k bits edge).flatMap
        (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (tupleAddress::checkedTupleScratch)) := by
  let fs := selectedTupleTerms G degree k bits edge
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.out=a.out++factorPrefix fs i ∧
      (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      b.rc store≤bits.length ∧ Cst b ∧ Fr a b (tupleAddress::checkedTupleScratch)
  have hset : ∀ i b v,I i b→I i (b.set tupleAddress v) := by
    rintro i b v ⟨bo,bs,br,bc,bf⟩
    exact ⟨bo,bs,br,Cst.of_fr (T := [tupleAddress]) bc (Fr.set _ _ (by simp)) (by decide),
      bf.trans (Fr.set _ _ (by simp))⟩
  have hcount : G^degree<2^C.Wd := by
    have hp : 0<G^degree := Nat.pow_pos (by omega)
    omega
  unfold emitTupleTerms
  refine (forS_spec' (C := C) tupleAddress tupleTotal (by decide)
    (emitCheckedTuple store edge) a (G^degree) hcount I
    (degree*((bits.length+5*(k+G)+160*B+530)+4)+50*degree+200) hset
    ⟨by simp [factorPrefix],rfl,hcursor,hc,Fr.refl _ _⟩ ht ?_).mono le_rfl ?_
  · intro i hi b ⟨bo,bs,br,bc,bfr⟩ bi bn
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
    refine (emitCheckedTuple_run C store edge G degree k B ⟨i,hi⟩ bits b bc hG
      ((bfr _ (by decide)).trans hb) bn bi ((bfr _ (by decide)).trans hd)
      ((bfr _ (by decide)).trans hk) (by rw [bram]; exact hram) br hbits haddress
      hfit hdfit hW hindex hB hBit).mono le_rfl ?_
    rintro z ⟨zo,zs,zr,zc,zfr⟩
    have hil : i<fs.length := by simpa [fs,selectedTupleTerms] using hi
    have zform : z.out=b.out++(toks fs[i]).flatMap tokWord := by
      simpa only [fs,selectedTupleTerms,List.getElem_ofFn] using zo
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
    have htake : fs.take (G^degree)=fs := List.take_of_length_le (by simp [fs,selectedTupleTerms])
    simpa only [factorPrefix,htake] using zo

end NearQuarticWires.StageCert.Tokens
