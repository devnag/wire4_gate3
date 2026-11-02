import Proof.Quartic.StageCert.TupleFactor

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: original selected-square factors in their actual addressed
bounded-tuple order. -/
def selectedTupleFactors (G degree k : ℕ) (bits : List Bool) (edge : Fin 8)
    (address : Fin (G^degree)) : List (Formula (17*G)) :=
  List.ofFn (fun i : Fin degree=>StagePrint.selectedSquare (by decide : 0<4)
    (fun g : Fin G=>bits.getD (k+g.val) false) edge (tupleAddressEquiv G degree address i))

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: a factor prefix consists of its literal original integer
postfix token bytes, retaining the unexpanded occurrence pool. -/
def factorPrefix {V : ℕ} (fs : List (Formula V)) (count : ℕ) : List Bool :=
  (fs.take count).flatMap (fun f=>(toks f).flatMap tokWord)

/-- `lem:maskpoly` and `lem:print`, paper/paper.tex: stream every actual factor of one bounded occurrence tuple. -/
def emitTupleFactors (store : Fin MM) (edge : Fin 8) : St VV MM :=
  forS tuplePosition newtonIndex (emitTupleFactor store edge)

/-- `lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: the complete original selected
factor stream is generated from the address and retained witness records,
with every rewind, digit operation and atom token charged. -/
theorem emitTupleFactors_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G degree k B : ℕ) (address : Fin (G^degree)) (bits : List Bool)
    (a : DS VV MM) (hc : Cst a) (hG : 1≤G)
    (hb : a.env atomCount=G) (hp : a.env tuplePower=G^degree)
    (ha : a.env tupleAddress=address.val) (hd : a.env newtonIndex=degree)
    (hk : a.env selectionStart=k) (hram : a.ram store=bits.map Bool.toNat)
    (hcursor : a.rc store≤bits.length) (hbits : k+G≤bits.length)
    (haddress : k+G≤2^C.Wd) (hfit : 2*G^degree≤2^C.Wd) (hdfit : degree<2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hBit : B+2<2^C.Wd) :
    Hs C (emitTupleFactors store edge) a
      (degree*((bits.length+5*(k+G)+160*B+530)+4)+4) (fun z=>
      z.out=a.out++(selectedTupleFactors G degree k bits edge address).flatMap
        (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (tuplePosition::tupleFactorScratch)) := by
  let fs := selectedTupleFactors G degree k bits edge address
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.out=a.out++factorPrefix fs i ∧ b.env tuplePower=G^(degree-i) ∧
      (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      b.rc store≤bits.length ∧ Cst b ∧ Fr a b (tuplePosition::tupleFactorScratch)
  have hset : ∀ i b v,I i b→I i (b.set tuplePosition v) := by
    rintro i b v ⟨bo,bp,bs,br,bc,bfr⟩
    exact ⟨bo,by simpa only [DS.set_env_ne _ _ (by decide : tuplePower≠tuplePosition)] using bp,
      bs,br,Cst.of_fr (T := [tuplePosition]) bc (Fr.set _ _ (by simp)) (by decide),
      bfr.trans (Fr.set _ _ (by simp))⟩
  have h0 : I 0 a := ⟨by simp [factorPrefix],by simpa using hp,rfl,hcursor,hc,Fr.refl _ _⟩
  unfold emitTupleFactors
  refine (forS_spec' (C := C) tuplePosition newtonIndex (by decide)
    (emitTupleFactor store edge) a degree hdfit I
    (bits.length+5*(k+G)+160*B+530) hset h0 hd ?_).mono le_rfl ?_
  · intro i hi b ⟨bo,bp,bs,br,bc,bfr⟩ bi bn
    have bG : b.env atomCount=G := (bfr _ (by decide)).trans hb
    have ba : b.env tupleAddress=address.val := (bfr _ (by decide)).trans ha
    have bk : b.env selectionStart=k := (bfr _ (by decide)).trans hk
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
    refine (emitTupleFactor_run C store edge G degree i address.val k B bits b bc hG hi
      bG bp ba bk (by rw [bram]; exact hram) br hbits haddress hfit hW hindex hB hBit).mono le_rfl ?_
    rintro z ⟨zo,zp,zs,zr,zc,zfr⟩
    have hf : (⟨address.val/G^(degree-1-i)%G,Nat.mod_lt _ (by omega)⟩ : Fin G)=
        tupleAddressEquiv G degree address ⟨i,hi⟩ := by
      apply Fin.ext
      exact (tupleAddress_digit G degree address ⟨i,hi⟩).symm
    have hil : i<fs.length := by simpa [fs,selectedTupleFactors] using hi
    have zform : z.out=b.out++(toks fs[i]).flatMap tokWord := by
      simpa only [hf,fs,selectedTupleFactors,List.getElem_ofFn] using zo
    refine ⟨⟨?_,?_,zs.trans bs,zr,zc,
      bfr.trans (zfr.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx))⟩,?_,?_⟩
    · rw [zform,bo]
      simp only [factorPrefix,List.take_succ_eq_append_getElem hil,List.flatMap_append,
        List.flatMap_singleton,List.append_assoc]
    · rw [zp]
      congr 1
      omega
    · rw [zfr _ (by decide)]
      exact bi
    · rw [zfr _ (by decide)]
      exact bn
  · rintro z ⟨⟨zo,_,zs,zr,zc,zfr⟩,_,_⟩
    refine ⟨?_,zs,zr,zc,zfr⟩
    have ht : fs.take degree=fs := List.take_of_length_le (by simp [fs,selectedTupleFactors])
    simpa only [factorPrefix,ht] using zo

end NearQuarticWires.StageCert.Tokens
