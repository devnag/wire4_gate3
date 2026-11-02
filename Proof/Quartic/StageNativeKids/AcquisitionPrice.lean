import Proof.Quartic.StageNativeKids.RolePrice

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces
open StageTuple StagePrint StagePrint.Header StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: copying
an affine source prefix, four binary context fields and one binary atom
has a linear finite-byte price, including the final input rewind. -/
theorem native_ready_cost_bound (base : List Bool) (context : List ℕ) (atom : ℕ)
    (hlen : context.length = 4) :
    roleSourceReadyCost base context atom ≤
      1000 * (base.length + (context.flatMap natWord).length + (natWord atom).length + 1) := by
  simp only [roleSourceReadyCost, roleSourceInputCost, appendPayloadCost,
    appendNaturalsCost, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_cons, List.length_nil, List.length_append, frame_length, hlen]
  omega

/-- `prop:time`, paper/paper.tex: the
original source's actual loader clock is linear in that original word. -/
theorem native_source_loader_price : Price NativeKidsRequest.structuralScale
    NativeKidsRequest.sourceLoadCost := by
  have hw := native_word_price
  change Price NativeKidsRequest.structuralScale (fun r => r.sourceLoadCost)
  simp only [NativeKidsRequest.sourceLoadCost, original_loader_cost]
  change Price NativeKidsRequest.structuralScale (fun r => 6 * r.word.length + 27)
  price_with structuralScale_pos

/-- `prop:time`, paper/paper.tex: the
acquired source loader pays only actual acquired finite source length. -/
theorem native_acquired_loader_price : Price NativeKidsRequest.structuralScale
    NativeKidsRequest.acquiredLoadCost := by
  have hw := native_acquired_price
  change Price NativeKidsRequest.structuralScale (fun r => r.acquiredLoadCost)
  simp only [NativeKidsRequest.acquiredLoadCost, original_loader_cost]
  change Price NativeKidsRequest.structuralScale (fun r => 6 * r.acquiredWord.length + 27)
  price_with structuralScale_pos

/-- `prop:time`, paper/paper.tex: real
role source preparation is polynomial in the original source bytes,
with no numeric radix or complete walk-code factor. -/
theorem native_ready_price : Price NativeKidsRequest.structuralScale (fun r =>
    roleSourceReadyCost ((baseHeaderValues r.header).flatMap natWord)
      [r.header.call.first.gates.length, r.header.call.second.gates.length,
        r.header.prepared.seedParameters.N, r.walkCode.val] r.atom.val) := by
  have hw := native_word_price
  have h : Price NativeKidsRequest.structuralScale (fun r => 1000 * (r.word.length + 1)) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  have hb := native_ready_cost_bound ((baseHeaderValues r.header).flatMap natWord)
    [r.header.call.first.gates.length, r.header.call.second.gates.length,
      r.header.prepared.seedParameters.N, r.walkCode.val] r.atom.val rfl
  have hc : ([r.header.call.first.gates.length, r.header.call.second.gates.length,
      r.header.prepared.seedParameters.N, r.walkCode.val].flatMap natWord) = r.contextWord := by
    simp [NativeKidsRequest.contextWord, List.append_assoc]
  rw [hc] at hb
  have hn := native_word_length r
  omega

/-- `prop:time`, paper/paper.tex: the
original five-field prefix is a literal portion of the complete source. -/
theorem native_prefix_price : Price NativeKidsRequest.structuralScale
    (fun r => (r.prefixFields.flatMap frame).length) :=
  native_word_price.mono fun r => by
    have h := congrArg List.length (source_prefix r)
    simp only [List.length_append, List.length_replicate] at h
    omega

/-- `prop:time`, paper/paper.tex: complete
cold source acquisition includes the actual loader, binary formatter,
real framed role machine and every acquired output byte and marker. -/
theorem native_acquire_price : Price NativeKidsRequest.structuralScale acquireBudget := by
  have hl := native_source_loader_price
  have hp := native_prefix_price
  have hr := native_role_payload_price
  have hf := native_role_budget_price
  have hs := native_ready_price
  change Price NativeKidsRequest.structuralScale (fun r => acquireBudget r)
  simp only [acquireBudget, acquireClock, sourceRoleClock, acquireFormatCost, frame_length]
  price_with structuralScale_pos

/-- `prop:time`, paper/paper.tex: the
selected original indexed source has a structural polynomial byte price,
using only a computed small original occurrence and the real call. -/
theorem native_selected_source_price : Price NativeKidsRequest.structuralScale (fun r =>
    (selectedSourceWord r.header.call.first.gates.length (r.toRowContext.originalIndex r.atom).val
      (callWord r.header.call)).length) := by
  have hi := native_occurrence_price
  have hc := native_call_price
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      2 * ((r.toRowContext.originalIndex r.atom).val + 1) + 1 + (callWord r.header.call).length) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  unfold selectedSourceWord
  rw [List.length_append, NearCubicGates.Close.CounterAsm.natWord_len]
  have hn := NearCubicGates.Close.Dispatch.natBitLength_le_succ
    (if r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val
      then (r.toRowContext.originalIndex r.atom).val - r.header.call.first.gates.length
      else (r.toRowContext.originalIndex r.atom).val)
  split_ifs at hn ⊢ <;> omega

/-- `prop:time`, paper/paper.tex: the
actual original-bank selector, source and header copies, and binary
width formatting have one unconditional structural polynomial price. -/
theorem native_bank_price : Price NativeKidsRequest.structuralScale bankBudget := by
  have hl := native_acquired_loader_price
  have hb := native_first_count_price
  have hi := native_occurrence_price
  have hc := native_call_price
  have hs := native_selected_source_price
  have hh := native_header_price
  have hw := native_nat_price native_width_price
  change Price NativeKidsRequest.structuralScale (fun r => bankBudget r)
  simp only [bankBudget, bankClock, bankBodyClock, bankSelectionClock, selectSourceClock,
    writeIndexedCost, copyHeaderClock, ← rowHeader_bytes, bankFormatClock, frame_length]
  price_with structuralScale_pos

end NearQuarticWires.StageNativeKids
