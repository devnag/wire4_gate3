import Proof.Quartic.StageLiftTokens.SourceGuards

/-!
# Entry from the original residue-source state

`lem:print` and Step3, paper/paper.tex:
the physical parameter fetch and metadata copies establish the precise
state used by the circuit, digit and amplifier loops. All original
fixed fields and the measured compact-prefix length are retained.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

theorem initialize_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : ResidueReady C r a E) :
    Hs C initializeResidue a 106 (fun b=>b.out=a.out ∧ SourceReady C r b E ∧
      b.ram=a.ram ∧ (∀store,store≠parameterStore→b.rc store=a.rc store) ∧
      (b.ip,b.kin,b.kout,b.kc)=(a.ip,a.kin,a.kout,a.kc) ∧
      Fr a b [t2,vJ,c0,selectionStart,chainRows,newtonTau]) := by
  have hw:=source_width E C.Wd h.envelope_pos h.width
  obtain ⟨b,n,he,hn,bk,bJ,bcod,_br,bs,bc,bfr⟩:=initializeResidue_run C r.child.selected.1 a h.constants
    h.parameterRecords h.chainCount (by omega)
  have hv : Valid C b := he.valid (by omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  simp only [StageMain.parameterRest,Prod.mk.injEq] at bs
  have hr : b.ram=a.ram := bs.2.2.1
  have hb : ResidueReady C r b E := by
    refine ⟨bc,hv,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.envelope_pos,
      h.occurrences_bound,h.exponent_bound,h.chains_bound,h.partition_bound,h.prime_bound,
      h.M1_bound,h.A_bound,h.factors_bound,h.witness_length,h.width⟩
    · rw [hr]; exact h.parameterRecords
    · rw [hr]; exact h.factorRecords
    · rw [hr]; exact h.witnessRecords
    · rw [hr]; exact h.indexRecords
    · exact (bfr _ (by decide)).trans h.exponent
    · exact (bfr _ (by decide)).trans h.chainCount
    · exact (bfr _ (by decide)).trans h.modulus
    · exact (bfr _ (by decide)).trans h.prime
    · exact (bfr _ (by decide)).trans h.signs
    · exact (bfr _ (by decide)).trans h.kind
    · exact (bfr _ (by decide)).trans h.occurrences
    · exact (bfr _ (by decide)).trans h.firstOccurrences
  have hrc : a.rc parameterStore≤46 := by
    simpa only [h.parameterRecords,parameterScalars_length] using h.valid.rc_le parameterStore
  refine ⟨b,n,he,by omega,bs.2.1,⟨hb,bk,bJ,bcod.trans h.signs⟩,hr,?_,?_,bfr⟩
  · intro store hs
    have hh:=congrFun bs.2.2.2.1 store
    simpa only [Function.update_of_ne hs] using hh
  · simp only [Prod.mk.injEq]
    exact ⟨bs.1,bs.2.2.2.2.1,bs.2.2.2.2.2.1,bs.2.2.2.2.2.2⟩

end NearQuarticWires.StageLiftTokens
