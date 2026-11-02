import Proof.Quartic.StageLiftTokens.ScoreOccurrence
import Proof.Quartic.StageCert.DigitOccurrenceLoop

/-!
# Original score occurrence stream

`lem:residue` and `lem:print`, paper/paper.tex: enumerate the unchanged concatenated occurrence pool
with unit coefficients on the chosen circuit and zero coefficients
on the other circuit, retaining every repeated occurrence.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator StageCert.Tokens

def sourceScoreOccurrenceForms (G circuit firstCount code : ℕ) : List (Formula (17*G)) :=
  List.ofFn fun g : Fin G => occurrenceWalkFormula G g.val g.isLt
    (selectedSummand circuit firstCount g.val 1 : ℤ) code

def emitScoreOccurrences : St VV MM := forS atomOccurrence atomCount emitScoreOccurrence

theorem emitScoreOccurrences_run (C : Ctx) (G circuit firstCount code Batom : ℕ)
    (a : DS VV MM) (hc : Cst a) (hb : a.env atomCount=G)
    (hcirc : a.env selectedCircuit=circuit) (hfirst : a.env firstGateCount=firstCount)
    (hcode : a.env newtonTau=code) (hW : 5≤C.Wd) (hindex : 17*G<2^C.Wd)
    (hB : ∀g<G,∀edge j,natBitLength (cornerRoleCode edge j*G+g)≤Batom)
    (hAtomFit : Batom+2<2^C.Wd) :
    Hs C emitScoreOccurrences a (G*(8*(40+160*Batom+640)+44)+4) (fun z=>
      z.out=a.out++(sourceScoreOccurrenceForms G circuit firstCount code).flatMap
        (fun f=>(toks f).flatMap tokWord) ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z (atomOccurrence::scoreOccurrenceScratch)) := by
  let fs := sourceScoreOccurrenceForms G circuit firstCount code
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.out=a.out++factorPrefix fs i ∧
    (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
    Cst b ∧ Fr a b (atomOccurrence::scoreOccurrenceScratch)
  have hset : ∀i b v,I i b→I i (b.set atomOccurrence v) := by
    rintro i b v ⟨bo,bs,bc,bfr⟩
    exact ⟨bo,bs,Cst.of_fr (T := [atomOccurrence]) bc (Fr.set _ _ (by simp)) (by decide),
      bfr.trans (Fr.set _ _ (by simp))⟩
  have hGfit : G<2^C.Wd := by omega
  unfold emitScoreOccurrences
  refine (forS_spec' (C := C) atomOccurrence atomCount (by decide)
    emitScoreOccurrence a G hGfit I (8*(40+160*Batom+640)+40) hset
    ⟨by simp [factorPrefix],rfl,hc,Fr.refl _ _⟩ hb ?_).mono le_rfl ?_
  · intro i hi b ⟨bo,bs,bc,bfr⟩ bi bn
    refine (emitScoreOccurrence_run C G i circuit firstCount code Batom b bc bn bi hi
      ((bfr _ (by decide)).trans hcirc) ((bfr _ (by decide)).trans hfirst)
      ((bfr _ (by decide)).trans hcode) hW hindex (hB i hi) hAtomFit).mono le_rfl ?_
    rintro z ⟨zo,zs,zc,zfr⟩
    have hil : i<fs.length := by simpa [fs,sourceScoreOccurrenceForms] using hi
    have zform : z.out=b.out++(toks fs[i]).flatMap tokWord := by
      simpa only [fs,sourceScoreOccurrenceForms,List.getElem_ofFn] using zo
    refine ⟨⟨?_,zs.trans bs,zc,
      bfr.trans (zfr.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx))⟩,?_,?_⟩
    · rw [zform,bo]
      simp only [factorPrefix,List.take_succ_eq_append_getElem hil,List.flatMap_append,
        List.flatMap_singleton,List.append_assoc]
    · rw [zfr _ (by decide)]; exact bi
    · rw [zfr _ (by decide)]; exact bn
  · rintro z ⟨⟨zo,zs,zc,zfr⟩,_,_⟩
    refine ⟨?_,zs,zc,zfr⟩
    have htake : fs.take G=fs := List.take_of_length_le (by simp [fs,sourceScoreOccurrenceForms])
    simpa only [factorPrefix,htake] using zo

end NearQuarticWires.StageLiftTokens
