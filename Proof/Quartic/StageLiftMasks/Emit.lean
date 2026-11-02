import Proof.Quartic.StageLiftMasks.Capacity
import Proof.Quartic.StageLiftMasks.Syntax

/-!
# One complete original tuple mask

`lem:maskpoly` and `lem:print`, paper/paper.tex: each loaded structural factor is combined
with the actual retained occurrence bits by the full signed Newton
and guarded-tuple emitter, with its original exponential count.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

theorem emitMask_avoids_store : ∀edge : Fin 8,∀s : Fin MM,s≠witnessStore→
    avoidsStore s (emitMask witnessStore edge) := by decide

noncomputable def originalMaskCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  maskSourceCost (Builder.allGates r.child.call).length r.child.selected.1.k r.child.selected.1.Xmax
    (2*(sourceEnvelope r+1)) (4*(sourceEnvelope r+1))
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length

theorem emitOriginalMask_run {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (edge : Fin 8) (a : DS VV MM) (h : PrintMasksReady width input L B r index a)
    (ht : a.env newtonTau=r.child.selected.1.tau)
    (hx : a.env maskLimit=r.child.selected.1.Xmax+1)
    (hk : a.env selectionStart=r.child.selected.1.k)
    (hs : a.env maskStructural=(StagePrint.callStructural r.child.call
      (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge).toNat) :
    Hs (structuralSourceContext B1 B2 width input L B) (emitMask witnessStore edge) a
      (originalMaskCost r) (fun b=>b.out=a.out++(toks (edgeMaskFormula r index edge)).flatMap tokWord ∧
        PrintMasksReady width input L B r index b ∧ MaskFrame a b) := by
  let C:=structuralSourceContext B1 B2 width input L B
  have hcap:=source_mask_capacity r width h.residue.width
  have hcursor : a.rc witnessStore≤(Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length := by
    simpa only [h.residue.witnessRecords,List.length_map] using h.residue.valid.rc_le witnessStore
  have hbits : r.child.selected.1.k+(Builder.allGates r.child.call).length≤
      (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length := by
    rw [source_witness_prefix_length]
    have hh := Nat.le_mul_of_pos_left (Builder.allGates r.child.call).length
      (by omega : 0<r.child.selected.1.J+1)
    omega
  obtain ⟨b,n,he,hn,bo,bs,_bcursor,bc,bfr⟩:=emitMask_run C witnessStore edge
    (Builder.allGates r.child.call).length r.child.selected.1.tau r.child.selected.1.Xmax
    r.child.selected.1.k (2*(sourceEnvelope r+1)) (4*(sourceEnvelope r+1))
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness)
    (StagePrint.callStructural r.child.call
      (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge)
    a h.residue.constants (print_originalPool_pos r) h.residue.occurrences ht hx hk hs
    h.residue.witnessRecords hcursor hbits hcap.address hcap.tuples hcap.newtonArithmetic
    hcap.minWidth hcap.atomIndex (fun g hg j=>source_atom_bits r g hg edge j) hcap.atomWord
    (source_newton_bits r) hcap.newtonWord
  simp only [Prod.mk.injEq] at bs
  have hf : MaskFrame a b := by
    refine ⟨bs.2.1,?_,bs.1,?_⟩
    · intro s hs'
      have hs3 : s≠witnessStore := by intro heq; subst s; exact hs' (by simp)
      exact (avoidsStore_spec he (emitMask_avoids_store edge s hs3)).2
    · intro x hx'
      exact bfr x ((show ∀x∈maskRegisters,x∉newtonIndex::maskDegreeScratch by decide) x hx')
  refine ⟨b,n,he,hn,?_,ready_of_frame h bc (ready_execution_valid h he) hf
    (bs.2.2.1.trans h.inputEmpty),hf⟩
  rw [retained_selection] at bo
  exact bo

end NearQuarticWires.StageLiftMasks
