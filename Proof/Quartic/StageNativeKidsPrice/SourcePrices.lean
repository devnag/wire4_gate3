import Proof.Quartic.StageNativeKidsPrice.Inputs
import Proof.Quartic.StageNativeKidsPrice.Arithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Dispatch
open StageNativeKids StageTuple StagePrint

attribute [local irreducible] RawBits.IndexedCallGateRequest.child compileL

macro "source_price" : tactic => `(tactic| price_with scale_pos)

/-- `prop:time`, paper/paper.tex: the actual
original compiler's field width has a fixed polynomial structural price. -/
theorem field_price : Price SourceCase.scale (fun a => a.source.child.W) := by
  have hn := arity_price
  have h : Price SourceCase.scale (fun a => 16*(a.request.header.call.n+1)^2) := by
    source_price
  exact h.mono fun a => (source_sizes a).2

/-- `prop:time`, paper/paper.tex: the dense
original weight count is exactly the original arity. -/
theorem weights_price : Price SourceCase.scale (fun a => a.source.child.weights.length) :=
  arity_price.mono fun a => (source_sizes a).1.le

/-- `prop:time`, paper/paper.tex: the bank
selector's numeric occurrence index obeys the original quartic census. -/
theorem index_price : Price SourceCase.scale (fun a => a.source.index.val) := by
  have hn := arity_price
  have h : Price SourceCase.scale (fun a => 2*a.request.header.call.n^4) := by source_price
  exact h.mono source_index

/-- `prop:time`, paper/paper.tex: bank-size
and occurrence codecs have uniform structural prices. -/
theorem bank_bits_price : Price SourceCase.scale
    (fun a => natBitLength (RawBits.originalCircuit a.second a.source.call).gates.length) := by
  have hn := arity_price
  have h : Price SourceCase.scale (fun a => 2*a.request.header.call.n^4+1) := by source_price
  exact h.mono fun a => (natBitLength_le_succ _).trans (by have := source_bank a; omega)

/-- `prop:time`, paper/paper.tex: the actual
original-source selector word contains one bounded occurrence codec and
the unchanged complete original call. -/
theorem source_word_price : Price SourceCase.scale (fun a => a.source.source.length) := by
  have hi := index_price
  have hc := call_price
  have h : Price SourceCase.scale
      (fun a => 2*(a.source.index.val+1)+1+(callWord a.request.header.call).length) := by source_price
  apply h.mono
  intro a
  have hb := natBitLength_le_succ a.source.index.val
  simp only [RawBits.IndexedCallGateRequest.source, source_call, source_suffix,
    List.append_nil, List.length_append, NearCubicGates.Close.Dispatch.natWord_length]
  omega

/-- `lem:print`, paper/paper.tex: the
selected original threshold word is a literal part of its source call. -/
theorem target_word_le (a : SourceCase) :
    (NearCubicGates.Close.Interfaces.intWord (a.source.child.target+1)).length ≤
      (callWord a.request.header.call).length := by
  have hg := (RawBits.gate_fields_le_bank
    (RawBits.originalCircuit a.second a.source.call).gates a.source.index).2.1
  have he : a.source.child.target+1 =
      (RawBits.originalCircuit a.second a.source.call).gates[a.source.index.val].threshold := by
    simp only [RawBits.IndexedCallGateRequest.child, originalChildRequest]
    omega
  rw [he]
  apply hg.trans
  rw [source_call]
  rcases a with ⟨r, b, h⟩
  cases b <;> simp only [RawBits.originalCircuit, Bool.false_eq_true, if_false, if_true,
    callWord, circuitWord, listWord, List.length_append] <;> omega

/-- `prop:time`, paper/paper.tex: exact
inclusive-threshold source bytes require no numeric threshold bound. -/
theorem target_word_price : Price SourceCase.scale
    (fun a => (NearCubicGates.Close.Interfaces.intWord (a.source.child.target+1)).length) :=
  call_price.mono target_word_le

/-- `prop:time`, paper/paper.tex: the
original logarithmic width is bounded by the original arity plus one. -/
theorem logarithm_price : Price SourceCase.scale
    (fun a => Nat.clog 2 (a.source.call.n+1)) := by
  have hn := arity_price
  have h : Price SourceCase.scale (fun a => a.request.header.call.n+1) := by source_price
  apply h.mono
  intro a
  rw [source_call]
  apply Nat.clog_le_of_le_pow
  exact Nat.lt_two_pow_self.le

/-- `imp:disjoint` and `prop:time`, paper/paper.tex: the complete original child count is charged
to the unchanged sharp child cap. -/
theorem child_count_price : Price SourceCase.scale
    (fun a => (compileL a.source.child.weights a.source.child.target).length) := by
  apply Price.of_le
  intro a
  have hc := originalChildRequest_length a.request.dimension_pos
    (Call.B0 a.request.header.call.n)
    (callAtoms a.request.header.call (a.request.toRowContext.originalIndex a.request.atom))
    (a.request.gate_bits (a.request.toRowContext.originalIndex a.request.atom))
  rw [← source_child a] at hc
  unfold SourceCase.scale NativeKidsRequest.originalSourceScale
  omega

/-- `lem:print`, paper/paper.tex: a flat
record stream costs its actual record count times its maximum byte width. -/
theorem flatMap_length_le {A : Type} (xs : List A) (f : A → List Bool) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith only [hh, ht]

/-- `lem:print`, paper/paper.tex: every
compiler child has its actual dense signed field count, including target. -/
theorem original_output_length (r : OriginalChildRequest) :
    r.output.length ≤ (compileL r.weights r.target).length *
      (2*((r.weights.length+1)*(r.W+1))+1) := by
  apply flatMap_length_le
  intro c hc
  have hn := compileL_length r.weights r.target c hc
  simp only [RepairOrdinary.frame_length, recBits, List.length_flatMap,
    SignedSortKey.binary_length, List.map_const', List.sum_replicate, smul_eq_mul, hn]
  exact le_rfl

/-- `prop:time`, paper/paper.tex: the full
original child stream retains its sharp count factor and dense field width. -/
theorem output_price : Price SourceCase.scale (fun a => a.source.child.output.length) := by
  have hc := child_count_price
  have hw := field_price
  have hn := weights_price
  have h : Price SourceCase.scale (fun a =>
      (compileL a.source.child.weights a.source.child.target).length *
        (2*((a.source.child.weights.length+1)*(a.source.child.W+1))+1)) := by source_price
  exact h.mono fun a => original_output_length a.source.child

/-- `prop:time`, paper/paper.tex: the actual
cold original compiler clock, including its physical field loader, has
a fixed polynomial price without an initialized child stream premise. -/
theorem compiler_price : Price SourceCase.scale (fun a => a.source.child.budget) := by
  have hw := field_price
  have hn := weights_price
  have h : Price SourceCase.scale
      (fun a => 2000000*(a.source.child.W+a.source.child.weights.length+1)^5) := by source_price
  exact h.mono fun a => Cells.ParameterArithmetic.originalChild_budget_polynomial a.source.child

end NearQuarticWires.StageNativeKidsPrice
