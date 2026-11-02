import Proof.Quartic.StageLiftMasks.Request
import Proof.Quartic.StageLiftTokens.Bounds
import Proof.Quartic.StageLiftTokens.StorePreservation

/-!
# Retained state during the eight original masks

`def:mask` and `lem:print`, paper/paper.tex: original source records and loop metadata survive
every real structural call and tuple enumeration. Reply buffers may
change, while the original input position and retained records do not.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

def maskRegisters : List (Fin VV) := [54,55,56,57,58,59,60,63,71,72,76,96,127]

structure MaskFrame (a b : DS VV MM) : Prop where
  records : b.ram=a.ram
  cursors : ∀s,s∉[parameterStore,witnessStore]→b.rc s=a.rc s
  input : b.ip=a.ip
  registers : ∀x∈maskRegisters,b.env x=a.env x

theorem MaskFrame.refl (a : DS VV MM) : MaskFrame a a :=
  ⟨rfl,fun _ _=>rfl,rfl,fun _ _=>rfl⟩

theorem MaskFrame.trans {a b d : DS VV MM} (h : MaskFrame a b) (g : MaskFrame b d) :
    MaskFrame a d := ⟨g.records.trans h.records,
      fun s hs=>(g.cursors s hs).trans (h.cursors s hs),g.input.trans h.input,
      fun x hx=>(g.registers x hx).trans (h.registers x hx)⟩

theorem MaskFrame.set (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : x∉maskRegisters) :
    MaskFrame a (a.set x v) := by
  refine ⟨rfl,fun _ _=>rfl,rfl,?_⟩
  intro y hy
  exact DS.set_env_ne _ _ (by intro he; subst y; exact hx hy)

theorem ready_of_frame {B1 B2 width L B : ℕ} {input : List Bool}
    {r : Greedy.PrintRequest B1 B2} {index : Fin (r.child.cellCall.seed.N^8)}
    {a b : DS VV MM} (h : PrintMasksReady width input L B r index a)
    (hc : Cst b) (hv : Valid (structuralSourceContext B1 B2 width input L B) b)
    (hf : MaskFrame a b) (hk : b.kin=[]) : PrintMasksReady width input L B r index b := by
  have hr : ResidueReady (structuralSourceContext B1 B2 width input L B)
      r b (sourceEnvelope r) := by
    refine ⟨hc,hv,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.residue.envelope_pos,
      h.residue.occurrences_bound,h.residue.exponent_bound,h.residue.chains_bound,
      h.residue.partition_bound,h.residue.prime_bound,h.residue.M1_bound,h.residue.A_bound,
      h.residue.factors_bound,h.residue.witness_length,h.residue.width⟩
    · rw [hf.records]; exact h.residue.parameterRecords
    · rw [hf.records]; exact h.residue.factorRecords
    · rw [hf.records]; exact h.residue.witnessRecords
    · rw [hf.records]; exact h.residue.indexRecords
    · exact (hf.registers _ (by decide)).trans h.residue.exponent
    · exact (hf.registers _ (by decide)).trans h.residue.chainCount
    · exact (hf.registers _ (by decide)).trans h.residue.modulus
    · exact (hf.registers _ (by decide)).trans h.residue.prime
    · exact (hf.registers _ (by decide)).trans h.residue.signs
    · exact (hf.registers _ (by decide)).trans h.residue.kind
    · exact (hf.registers _ (by decide)).trans h.residue.occurrences
    · exact (hf.registers _ (by decide)).trans h.residue.firstOccurrences
  refine ⟨hr,?_,?_,?_,hk,?_,h.sourceRoom,h.sourceBudget⟩
  · rw [hf.records]; exact h.preparedRecords
  · exact (hf.registers _ (by decide)).trans h.preparedBytes
  · exact (hf.cursors _ (by decide)).trans h.preparedCursor
  · exact (hf.registers _ (by decide)).trans h.walkOrdinal

theorem ready_execution_valid {B1 B2 width L B : ℕ} {input : List Bool}
    {r : Greedy.PrintRequest B1 B2} {index : Fin (r.child.cellCall.seed.N^8)}
    {a b : DS VV MM} {s : St VV MM} {n : ℕ}
    (h : PrintMasksReady width input L B r index a)
    (he : Ex (structuralSourceContext B1 B2 width input L B) s a b n) :
    Valid (structuralSourceContext B1 B2 width input L B) b := by
  have hw:=StageLiftTokens.source_width _ _ h.residue.envelope_pos h.residue.width
  exact he.valid (by omega)
    (fun q hq=>(wf_out_len (structuralSourceContext B1 B2 width input L B).K.wf q).trans (by omega))
    h.residue.valid

end NearQuarticWires.StageLiftMasks
