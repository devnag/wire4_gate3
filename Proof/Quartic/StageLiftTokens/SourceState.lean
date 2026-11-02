import Proof.Quartic.StageLiftTokens.Initialize
import Proof.Quartic.StageLiftTokens.ScoreDock
import Proof.Quartic.StageLiftTokens.WitnessDock

/-!
# Retained residue-source state

`lem:print` and Step 3, paper/paper.tex: all original parameter, witness and normalized-index
records remain fixed during the repeated Fermat and amplifier passes.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

def sourceRegisters : List (Fin VV) :=
  [54,55,56,57,58,59,60,63,71,72,76,96,99,107,125,127]

structure SourceReady {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (E : ℕ) : Prop extends ResidueReady C r a E where
  partition : a.env selectionStart=r.child.selected.1.k
  rows : a.env chainRows=r.child.selected.1.J
  signCopy : a.env newtonTau=printPatternCode r.pattern

structure SourceFrame (a b : DS VV MM) : Prop where
  records : b.ram=a.ram
  cursors : ∀store,store∉[parameterStore,factorStore,witnessStore,indexStore]→b.rc store=a.rc store
  streams : (b.ip,b.kin,b.kout,b.kc)=(a.ip,a.kin,a.kout,a.kc)
  registers : ∀x∈sourceRegisters,b.env x=a.env x

theorem SourceFrame.refl (a : DS VV MM) : SourceFrame a a :=
  ⟨rfl,fun _ _=>rfl,rfl,fun _ _=>rfl⟩

theorem SourceFrame.trans {a b d : DS VV MM} (h : SourceFrame a b) (g : SourceFrame b d) :
    SourceFrame a d :=
  ⟨g.records.trans h.records,fun s hs=>(g.cursors s hs).trans (h.cursors s hs),
    g.streams.trans h.streams,fun x hx=>(g.registers x hx).trans (h.registers x hx)⟩

theorem SourceFrame.of_rest {a b : DS VV MM} {T : List (Fin VV)}
    (hr : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc))
    (hf : Fr a b T) (ht : ∀x∈sourceRegisters,x∉T) : SourceFrame a b := by
  simp only [Prod.mk.injEq] at hr
  exact ⟨hr.2.1,fun s _=>congrFun hr.2.2.1 s,
    by simp only [Prod.mk.injEq]; exact ⟨hr.1,hr.2.2.2.1,hr.2.2.2.2.1,hr.2.2.2.2.2⟩,
    fun x hx=>hf x (ht x hx)⟩

theorem SourceReady.of_frame {B1 B2 : ℕ} {C : Ctx} {r : Greedy.PrintRequest B1 B2}
    {a b : DS VV MM} {E : ℕ} (ha : SourceReady C r a E)
    (hc : Cst b) (hv : Valid C b) (hf : SourceFrame a b) : SourceReady C r b E := by
  have he (x : Fin VV) (hx : x∈sourceRegisters) : b.env x=a.env x := hf.registers x hx
  refine ⟨⟨hc,hv,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,ha.envelope_pos,
    ha.occurrences_bound,ha.exponent_bound,ha.chains_bound,ha.partition_bound,ha.prime_bound,
    ha.M1_bound,ha.A_bound,ha.factors_bound,ha.witness_length,ha.width⟩,?_,?_,?_⟩
  · rw [hf.records]; exact ha.parameterRecords
  · rw [hf.records]; exact ha.factorRecords
  · rw [hf.records]; exact ha.witnessRecords
  · rw [hf.records]; exact ha.indexRecords
  · exact (he _ (by decide)).trans ha.exponent
  · exact (he _ (by decide)).trans ha.chainCount
  · exact (he _ (by decide)).trans ha.modulus
  · exact (he _ (by decide)).trans ha.prime
  · exact (he _ (by decide)).trans ha.signs
  · exact (he _ (by decide)).trans ha.kind
  · exact (he _ (by decide)).trans ha.occurrences
  · exact (he _ (by decide)).trans ha.firstOccurrences
  · exact (he _ (by decide)).trans ha.partition
  · exact (he _ (by decide)).trans ha.rows
  · exact (he _ (by decide)).trans ha.signCopy

end NearQuarticWires.StageLiftTokens
