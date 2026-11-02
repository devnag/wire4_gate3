import Proof.Quartic.StageMainMask.EntryWordBounds
import Proof.Quartic.StageMainMask.NativeEntry

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

private theorem shift_cube (v S : ℕ) (hS : 1 ≤ S) (hv : v ≤ S) :
    3000 * (v + 1) ^ 3 ≤ 24000 * S ^ 3 := by
  calc
    _ ≤ 3000 * (2 * S) ^ 3 := by gcongr; omega
    _ = _ := by ring

private theorem shift_square (v S : ℕ) (hS : 1 ≤ S) (hv : v ≤ S) :
    4000 * (v + 1) ^ 2 ≤ 16000 * S ^ 2 := by
  calc
    _ ≤ 4000 * (2 * S) ^ 2 := by gcongr; omega
    _ = _ := by ring

private theorem translation_arithmetic (w k S : ℕ) (hS : 1 ≤ S) (hw : w ≤ S) (hk : k ≤ S) :
    k * (w + 6 * k + 21) + 4 ≤ 32 * S ^ 3 := by
  have h1 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h0 : 1 ≤ S ^ 3 := Nat.pow_pos hS
  calc
    _ ≤ S * (S + 6 * S + 21) + 4 := by gcongr
    _ ≤ _ := by nlinarith only [h1, h2, h0]

/-- `prop:time`, paper/paper.tex: a single linear
bound on the actual finite Entry source covers every literal subroutine
request and every binary metadata field. -/
noncomputable def entrySourceScale {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  20 * ((entryWord r).length + 2)

/-- `prop:time`, paper/paper.tex: the actual
finite source and original dimension fit the shared source-word scale. -/
theorem entrySourceScale_bounds {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    1 ≤ entrySourceScale r ∧ (entryWord r).length + 1 ≤ entrySourceScale r ∧
      r.call.n + 1 ≤ entrySourceScale r := by
  have h := (entrySource_lengths r).2.2.2.2
  unfold entrySourceScale
  omega

/-- `prop:time`, paper/paper.tex: actual finite
source measurement, retention, witness translation and every coordinate
of all four original points have polynomial source-word clock. -/
theorem entryPointCoreSteps_le {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    entryPointCoreSteps r ≤ 1000000 * (entrySourceScale r) ^ 4 := by
  let S := entrySourceScale r
  have hs := entrySourceScale_bounds r
  have hS : 1 ≤ S := hs.1
  have hl : (entryWord r).length ≤ S := by dsimp only [S]; omega
  have hn : r.call.n + 1 ≤ S := hs.2.2
  have hsrc := entrySource_lengths r
  have hc : (callWord r.call).length ≤ S := hsrc.1.trans hl
  have hp : (Program.parametersWord r.selected.1).length ≤ S := hsrc.2.2.2.1.trans hl
  have hw : (Program.witnessPrefix r.call r.selected.1 r.witness).length ≤ S := hsrc.2.2.1.trans hl
  have hprep : (compactInput r.call r.selected.1
      (Program.witnessPrefix r.call r.selected.1 r.witness)).length ≤ S := by
    rw [← prepWord_eq_compact r.dispatched]
    exact hsrc.2.1.trans hl
  have hprefix : (preparedPrefixWord r.call r.selected.1).length ≤ S :=
    (StageMain.Runtime.compact_lengths r.call r.selected.1
      (Program.witnessPrefix r.call r.selected.1 r.witness)).2.2.1.trans hprep
  have hk : r.selected.1.k ≤ S := by
    have hh := entrySelection_fits r
    omega
  have hi : initializeCost r.call r.selected.1
      (Program.witnessPrefix r.call r.selected.1 r.witness)
      (compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)).length ≤
        110000 * S ^ 3 := by
    have hf := structuralFormatterSteps_le (entryStructuralRequest r) S hS (entryRequest_words r).1
    apply le_trans (b := structuralFormatterSteps (entryStructuralRequest r)) _ hf
    unfold structuralFormatterSteps structuralPrepareSteps
    dsimp only [entryStructuralRequest]
    omega
  have hc3 := shift_cube (callWord r.call).length S hS hc
  have hp2 := shift_square (Program.parametersWord r.selected.1).length S hS hp
  have ht : StagePrint.Header.translationCost
      (Program.witnessPrefix r.call r.selected.1 r.witness).length r.selected.1.k ≤ 32 * S ^ 3 := by
    exact translation_arithmetic _ _ S hS hw hk
  have h3 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h03 : 1 ≤ S ^ 3 := Nat.pow_pos hS
  have hsize : sizedEntrySourceSteps r ≤ 200000 * S ^ 3 := by
    unfold sizedEntrySourceSteps
    omega
  have hfields : ∀ v ∈ [r.column.val, r.fieldValue.val], natBitLength v ≤ S := by
    have hcol := NearCubicGates.Close.Dispatch.natBitLength_le_len r.column.val
    have hval := NearCubicGates.Close.Dispatch.natBitLength_le_len r.fieldValue.val
    have hlen : (natWord r.column.val).length + (natWord r.fieldValue.val).length ≤ S := by
      have hentry : (entryWord r).length = (Program.prepWord B1 B2 r.call r.witness).length +
          (natWord r.column.val).length + (natWord r.fieldValue.val).length := by
        simp only [entryWord, List.length_append]
      omega
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> omega
  have hr := StageGamma.readFieldsCost_le [r.column.val, r.fieldValue.val] S hfields
  simp only [List.length_cons, List.length_nil] at hr
  have hcorner : pointCornerCost (entryPointRequest r false false) ≤ 5000 * S ^ 4 := by
    have h4 : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
    have h04 : 1 ≤ S ^ 4 := Nat.pow_pos hS
    change r.call.n * (500 * (r.call.n + 1) ^ 3 + 9) + 14 ≤ _
    calc
      _ ≤ S * (500 * S ^ 3 + 9) + 14 := by gcongr; omega
      _ ≤ _ := by ring_nf; omega
  have h34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ≤ S ^ 4 := Nat.le_self_pow (by decide) _
  have h04 : 1 ≤ S ^ 4 := Nat.pow_pos hS
  have hbit := NearCubicGates.Close.Dispatch.natBitLength_le_succ r.call.n
  unfold entryPointCoreSteps
  change _ ≤ 1000000 * S ^ 4
  omega

/-- `prop:time`, paper/paper.tex: source writing,
reply decoding and the constant scalar logic are linear in the finite
original source scale before the three actual call clocks are added. -/
theorem evaluationSteps_source_le {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    evaluationSteps r 0 0 ≤ 10000 * entrySourceScale r := by
  let S := entrySourceScale r
  have hs := entrySourceScale_bounds r
  have hS : 1 ≤ S := hs.1
  have hl : (entryWord r).length + 1 ≤ S := hs.2.1
  have hsrc := entrySource_lengths r
  have hu := structural_index_bits (entryStructuralRequest r)
  have hp := pointPacked_bits (entryPointRequest r true true)
  have hf := populationInputFields_bits r
  have h0 := hf (38, r.selected.1.k) (by simp [populationInputFields])
  have h1 := hf (114, entryCorners r 0) (by simp [populationInputFields])
  have h2 := hf (115, entryCorners r 1) (by simp [populationInputFields])
  have h3 := hf (116, entryCorners r 2) (by simp [populationInputFields])
  have h4 := hf (117, entryCorners r 3) (by simp [populationInputFields])
  dsimp only [Prod.snd] at h0 h1 h2 h3 h4
  have hpop := entryPopulation_bits r
  have hpop' : natBitLength (entryPopulationRequest r).value ≤ S := by
    dsimp only [S, entrySourceScale]
    omega
  change natBitLength (entryPredicateRequest r).point ≤ r.call.n + 1 at hp
  change natBitLength (entryPosition r).1.val ≤ (Program.prepWord B1 B2 r.call r.witness).length ∧
    natBitLength (entryPosition r).2.val ≤ (Program.prepWord B1 B2 r.call r.witness).length at hu
  unfold evaluationSteps
  simp only [populationInputFields, naturalFieldsCost,
    NearCubicGates.Close.Dispatch.natWord_length, Nat.mul_zero, Nat.add_zero]
  change _ ≤ 10000 * S
  omega

end NearQuarticWires.StageMainMask
