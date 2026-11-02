import Proof.Quartic.StageCert.DigitWalkForm

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testX` and `lem:print`, paper/paper.tex: physical occurrence and record scratch for the exact
witness-selected population formula. -/
def populationSourceScratch : List (Fin VV) :=
  [sourceRecordLimit,selectedTokenBit,sourceRecordIndex,sourceRecordDiscard,atomRole,atomValue]++
    StageLift.tokenScratch

/-- `eq:testX` and `lem:print`, paper/paper.tex: emit the actual selected square of every original
occurrence by reading its retained selection bit. -/
def emitPopulationSquares (store : Fin MM) (edge : Fin 8) : St VV MM :=
  forS atomOccurrence atomCount (emitSourceSquare store edge)

/-- `eq:testX`, `lem:print` and `prop:time`, paper/paper.tex: the complete original
population summand list is serialized from physical witness records,
with every source prefix scan and repeated gate occurrence charged. -/
theorem emitPopulationSquares_run (C : Ctx) (store : Fin MM) (edge : Fin 8)
    (G k B : ℕ) (bits : List Bool) (a : DS VV MM) (hc : Cst a)
    (hG : 1≤G) (hb : a.env atomCount=G) (hk : a.env selectionStart=k)
    (hram : a.ram store=bits.map Bool.toNat) (hcursor : a.rc store≤bits.length)
    (hbits : k+G≤bits.length) (haddress : k+G≤2^C.Wd)
    (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀j,natBitLength (cornerRoleCode edge j*G+g)≤B) (hfit : B+2<2^C.Wd) :
    Hs C (emitPopulationSquares store edge) a
      (G*(bits.length+5*(k+G)+160*B+524)+4) (fun z=>
      z.out=a.out++(List.ofFn (StagePrint.selectedSquare (by decide : 0<4)
        (fun i : Fin G=>bits.getD (k+i.val) false) edge)).flatMap
          (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
      z.rc store≤bits.length ∧ Cst z ∧ Fr a z (atomOccurrence::populationSourceScratch)) := by
  let fs := List.ofFn (StagePrint.selectedSquare (by decide : 0<4)
    (fun i : Fin G=>bits.getD (k+i.val) false) edge)
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.out=a.out++factorPrefix fs i ∧
    (b.ip,b.ram,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.kin,a.kout,a.kc) ∧
    b.rc store≤bits.length ∧ Cst b ∧ Fr a b (atomOccurrence::populationSourceScratch)
  have hset : ∀ i b v,I i b→I i (b.set atomOccurrence v) := by
    rintro i b v ⟨bo,bs,br,bc,bfr⟩
    exact ⟨bo,bs,br,Cst.of_fr (T := [atomOccurrence]) bc (Fr.set _ _ (by simp)) (by decide),
      bfr.trans (Fr.set _ _ (by simp))⟩
  have hGfit : G<2^C.Wd := by omega
  unfold emitPopulationSquares
  refine (forS_spec' (C := C) atomOccurrence atomCount (by decide)
    (emitSourceSquare store edge) a G hGfit I
    (bits.length+5*(k+G)+160*B+520) hset
    ⟨by simp [factorPrefix],rfl,hcursor,hc,Fr.refl _ _⟩ hb ?_).mono le_rfl ?_
  · intro i hi b ⟨bo,bs,br,bc,bfr⟩ bi bn
    have bram : b.ram=a.ram := congrArg (fun q=>q.2.1) bs
    refine (emitSourceSquare_run C store edge G i k B hi bits b bc bn bi
      ((bfr _ (by decide)).trans hk) (by rw [bram]; exact hram) (by omega)
      (by omega) hW hindex (hB i hi) hfit).mono (by omega) ?_
    rintro z ⟨zo,zs,zr,zc,zfr⟩
    have hil : i<fs.length := by simpa [fs] using hi
    have zform : z.out=b.out++(toks fs[i]).flatMap tokWord := by
      simpa only [fs,List.getElem_ofFn] using zo
    refine ⟨⟨?_,zs.trans bs,by omega,zc,
      bfr.trans (zfr.weaken (by decide))⟩,?_,?_⟩
    · rw [zform,bo]
      simp only [factorPrefix,List.take_succ_eq_append_getElem hil,List.flatMap_append,
        List.flatMap_singleton,List.append_assoc]
    · rw [zfr _ (by decide)]
      exact bi
    · rw [zfr _ (by decide)]
      exact bn
  · rintro z ⟨⟨zo,zs,zr,zc,zfr⟩,_,_⟩
    refine ⟨?_,zs,zr,zc,zfr⟩
    have htake : fs.take G=fs := List.take_of_length_le (by simp [fs])
    simpa only [factorPrefix,htake] using zo

end NearQuarticWires.StageCert.Tokens
