import Proof.Quartic.StageNativeKids.AcquisitionPrice
import Proof.Quartic.StageNativeKidsTail.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces
open StageTuple StagePrint StageNativeKidsPrice

/-- `prop:time`, paper/paper.tex: the
unchanged sharp original-child cap is directly included in the one-atom
source resource, rather than replaced by any degree-dependent census. -/
theorem native_cap_price : Price NativeKidsRequest.structuralScale
    (fun r => Cells.childCap r.header.call.n (Call.B0 r.header.call.n)) :=
  Price.of_le (by intro r; unfold NativeKidsRequest.structuralScale NativeKidsRequest.originalSourceScale; omega)

/-- `imp:disjoint` and `prop:time`, paper/paper.tex: the actual computed child count retains the
original sharp cap even when the selected child pool is empty. -/
theorem native_kid_count_price : Price NativeKidsRequest.structuralScale
    (fun r => (r.toRowContext.nativeKids r.atom).length) :=
  native_cap_price.mono NativeKidsRequest.originalKids_cap

/-- `prop:time`, paper/paper.tex: bounded
dense original rows bound their actual flattened signed-field census. -/
theorem native_flatten_bound (rows : List (List ℤ)) (B : ℕ)
    (hb : ∀ row ∈ rows, row.length ≤ B) : rows.flatten.length ≤ rows.length * B := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hh := hb row (by simp)
    have ht := ih (fun x hx => hb x (by simp [hx]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    nlinarith only [hh, ht]

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the actual native signed-field census is at
most the original child cap times the original dense row dimension. -/
theorem native_field_count_bound (r : NativeKidsRequest) :
    r.resizeTailRequest.stream.fieldCount ≤
      Cells.childCap r.header.call.n (Call.B0 r.header.call.n) * (2 * r.header.call.n + 1) := by
  have hf := native_flatten_bound (r.toRowContext.nativeKids r.atom) (2 * r.header.call.n + 1)
    (by intro row hr
        rw [r.toRowContext.nativeKids_row_length r.atom row hr]
        have hd := (StageNativeWidth.nativeDimensions_le r.toRowContext).1
        omega)
  exact hf.trans (Nat.mul_le_mul_right _ r.originalKids_cap)

/-- `prop:time`, paper/paper.tex: the
actual native signed-field census has one fixed structural price. -/
theorem native_field_count_price : Price NativeKidsRequest.structuralScale
    (fun r => r.resizeTailRequest.stream.fieldCount) := by
  have hc := native_cap_price
  have hn := native_arity_price
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      Cells.childCap r.header.call.n (Call.B0 r.header.call.n) * (2 * r.header.call.n + 1)) := by
    price_with structuralScale_pos
  exact h.mono native_field_count_bound

/-- `prop:time`, paper/paper.tex: the
actual common source-field width is quadratic in original arity. -/
theorem native_input_width_price : Price NativeKidsRequest.structuralScale
    (fun r => r.toRowContext.nativeFieldWidth) := by
  have hn := native_arity_price
  have h : Price NativeKidsRequest.structuralScale (fun r => 16 * (r.header.call.n + 1)^2) := by
    price_with structuralScale_pos
  exact h.mono fun r => StageNativeWidth.nativeFieldWidth_le r.toRowContext

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual tail input has a structural
finite-byte price, including its computed count, width and end marker. -/
theorem native_tail_word_price : Price NativeKidsRequest.structuralScale
    (fun r => r.resizeTailRequest.word.length) := by
  have hc := native_nat_price native_kid_count_price
  have hf := native_field_count_price
  have hi := native_input_width_price
  have hw := native_width_price
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      (natWord (r.toRowContext.nativeKids r.atom).length).length +
        6 * (r.resizeTailRequest.stream.fieldCount + 1) *
          (r.toRowContext.nativeFieldWidth + r.outputWidth + 1)) := by
    price_with structuralScale_pos
  apply h.mono
  intro r
  have hs := r.resizeTailRequest.stream.word_length_le
  change (natWord (r.toRowContext.nativeKids r.atom).length ++ r.resizeTailRequest.stream.word).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add_left hs _

/-- `lem:print` and `prop:time`, paper/paper.tex: the once-only actual stream-resize tail
has an unconditional structural polynomial budget, retaining all signed
fields, original child order and the physically computed count. -/
theorem native_tail_price : Price NativeKidsRequest.structuralScale
    (fun r => r.resizeTailRequest.budget) := by
  have hc := native_nat_price native_kid_count_price
  have hf := native_field_count_price
  have hi := native_input_width_price
  have hw := native_width_price
  have h : Price NativeKidsRequest.structuralScale (fun r =>
      100000000 * (StageResize.resizeCostConstant + 8)^2 *
        (r.resizeTailRequest.stream.fieldCount + 1)^2 *
        (r.toRowContext.nativeFieldWidth + r.outputWidth +
          (natWord (r.toRowContext.nativeKids r.atom).length).length + 1)^6) := by
    price_with structuralScale_pos
  exact h.mono fun r => StageNativeKidsTail.tailBudget_polynomial r.resizeTailRequest

/-- `prop:time`, paper/paper.tex: the
computed tagged bank source has a polynomial byte price in the original
finite source and actual widths, independently of numeric walk values. -/
theorem native_bank_word_price : Price NativeKidsRequest.structuralScale
    (fun r => r.bankWord.length) := by
  have hs := native_selected_source_price
  have hh := native_header_price
  have hw := native_nat_price native_width_price
  simp only [NativeKidsRequest.bankWord, poolSourceWord, Top.loadRec,
    List.length_cons, List.length_nil, List.length_append, frame_length]
  price_with structuralScale_pos

/-- `prop:time`, paper/paper.tex: at the
actual original normalization bound, the retained child cap can be
absorbed into a fixed cubic source-and-arity polynomial; no degree or
walk-magnitude power is introduced. -/
theorem native_structural_scale_bound (r : NativeKidsRequest) :
    r.structuralScale ≤ 40 * (r.word.length + r.header.call.n + r.outputWidth + 1)^3 := by
  let S := r.word.length + r.header.call.n + r.outputWidth + 1
  have hp : 1 ≤ S := by dsimp [S]; omega
  have hi : r.word.length + r.header.call.n + 1 ≤ S := by dsimp [S]; omega
  have hc := (originalSourceScale_polynomial r).trans
    (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hi 3))
  have hw : r.outputWidth + 1 ≤ S := by dsimp [S]; omega
  have hS : S ≤ S^3 := Nat.le_self_pow (by decide) S
  change r.originalSourceScale + r.outputWidth + 1 ≤ 40 * S^3
  omega

end NearQuarticWires.StageNativeKids
