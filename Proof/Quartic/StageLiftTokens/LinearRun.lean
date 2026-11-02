import Proof.Quartic.StageLiftTokens.SourceGuards
import Proof.Quartic.StageLiftTokens.StorePreservation

/-!
# Actual retained-source score and digit runs

`lem:residue`, `eq:testE` and `lem:print`, paper/paper.tex: the original Y and digit formulas
are emitted by the real occurrence scans with every operand obtained
from its retained source and every loop guard derived from the envelope.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Cells NearCubicGates.Close.Tabulator
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

theorem original_pattern (pattern : Cycle.SignPattern 4) :
    StageCertTests.patternOfCode (printPatternCode pattern)=pattern := by
  funext i
  exact printPatternCode_testBit pattern i

theorem emitScore_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env selectedCircuit=j.val) :
    Hs C emitScoreWalkForm a (linearSourceCost E) (fun b=>
      b.out=a.out++(toks (StagePrint.callWalkFormula r.child.call j (fun _=>1) r.pattern)).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b scoreWalkScratch) := by
  obtain ⟨b,n,he,hn,bo,bs,bc,bfr⟩ := emitScoreWalkForm_run C
    (Builder.allGates r.child.call).length j.val r.child.call.first.gates.length
    (printPatternCode r.pattern) (sourceBits E) a h.constants h.occurrences hj h.firstOccurrences
    h.signCopy h.width_five h.atom_room h.atom_bits h.bits_room
  have hf : SourceFrame a b := SourceFrame.of_rest bs bfr (by decide)
  have hv : Valid C b := he.valid (by have hh:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  refine ⟨b,n,he,hn.trans (score_cost_le _ E h.occurrences_bound),?_,
    h.of_frame bc hv hf,hf,bfr⟩
  simpa only [source_score_formula_eq_builder,original_pattern] using bo

theorem emitDigit_ready (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (row : Fin (r.child.selected.1.J-1+1))
    (hj : a.env selectedCircuit=j.val) (hr : a.env requestedChainRow=row.val) :
    Hs C (emitDigitWalkForm witnessStore factorStore) a (linearSourceCost E) (fun b=>
      b.out=a.out++(toks (StagePrint.callWalkFormula r.child.call j
        (StagePrint.callDigitWeights r.child.call
          (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) r.child.witness j row)
        r.pattern)).flatMap tokWord ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ Fr a b (atomOccurrence::digitOccurrenceScratch)) := by
  let bits := Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness
  let p := r.child.selected.1
  have hp := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hrow : row.val<p.J := by have hi:=row.isLt; have hJ:=hp.J_pos; dsimp only [p]; omega
  have hwcur : a.rc witnessStore≤bits.length := by
    simpa only [h.witnessRecords,List.length_map] using h.valid.rc_le witnessStore
  have hfcur : a.rc factorStore≤p.factors.length := by
    simpa only [h.factorRecords] using h.valid.rc_le factorStore
  obtain ⟨b,n,he,hn,bo,bs,_bw,_br,bc,bfr⟩ := emitDigitWalkForm_run C witnessStore factorStore (by decide)
    (Builder.allGates r.child.call).length row.val p.J p.k j.val r.child.call.first.gates.length
    (printPatternCode r.pattern) (sourceBits E) (sourceBits E) bits p.factors a h.constants
    (print_originalPool_pos r) h.occurrences hr h.rows h.partition hj h.firstOccurrences h.signCopy
    hrow h.factor_length h.witnessRecords h.factorRecords hwcur hfcur
    (by rw [source_witness_prefix_length]) h.witness_room h.chain_room
    (h.rate_room row.val) h.width_five h.atom_room h.atom_bits h.bits_room
    (fun g _=>source_coefficient_bits bits p.factors E _ row.val p.J p.k g j.val
      r.child.call.first.gates.length h.envelope_pos h.factors_bound) h.bits_room
  have hf : SourceFrame a b := by
    simp only [Prod.mk.injEq] at bs
    refine ⟨bs.2.1,?_,?_,fun x hx=>bfr x ?_⟩
    · intro store hs
      exact digitForm_other_cursors he store (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs ⊢
        exact ⟨hs.2.2.1,hs.2.1⟩)
    · simp only [Prod.mk.injEq]
      exact ⟨bs.1,bs.2.2.1,bs.2.2.2.1,bs.2.2.2.2⟩
    · exact (by decide : ∀x∈sourceRegisters,x∉atomOccurrence::digitOccurrenceScratch) x hx
  have hv : Valid C b := he.valid (by have hh:=h.width_five; omega)
    (fun s hs=>(wf_out_len C.K.wf s).trans (by omega)) h.valid
  refine ⟨b,n,he,hn.trans (digit_cost_le _ E bits.length p.factors.length
    h.occurrences_bound h.witness_length (by rw [h.factor_length]; have hh:=h.chains_bound; omega)),
    ?_,h.of_frame bc hv hf,hf,bfr⟩
  dsimp only [bits,p] at bo
  rw [retained_digit_formula_eq r.child.call hp r.child.witness j row,original_pattern] at bo
  exact bo

end NearQuarticWires.StageLiftTokens
