import Proof.Quartic.StageMainMask.Evaluation
import Proof.Quartic.StageMainMask.StructuralSizes
import Proof.Quartic.StageMain.CallSizeWords

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift StagePullback

/-- `prop:time`, paper/paper.tex: every retained
original source record and the original arity is bounded by the literal
finite numeric-entry word, before any point or gate is evaluated. -/
theorem entrySource_lengths {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (callWord r.call).length ≤ (entryWord r).length ∧
    (Program.prepWord B1 B2 r.call r.witness).length ≤ (entryWord r).length ∧
    (Program.witnessPrefix r.call r.selected.1 r.witness).length ≤ (entryWord r).length ∧
    (Program.parametersWord r.selected.1).length ≤ (entryWord r).length ∧
    r.call.n ≤ (entryWord r).length := by
  have hp := congrArg List.length (prepWord_eq_compact r.dispatched (w := r.witness))
  simp only [compactInput, preparedPrefixWord, List.length_cons, List.length_append,
    frame_length] at hp
  have he : (entryWord r).length = (Program.prepWord B1 B2 r.call r.witness).length +
      (natWord r.column.val).length + (natWord r.fieldValue.val).length := by
    simp only [entryWord, List.length_append]
  have hn := Cells.dispatched_n_le_callWord r.dispatched
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- `imp:partition` and `prop:time`, paper/paper.tex: every physically computed packed point has
binary length at most one more than the original coordinate dimension. -/
theorem pointPacked_bits (q : PointRequest) : natBitLength q.packed ≤ q.parameters.n + 1 := by
  have hp : q.packed < 2 ^ q.parameters.n := by
    simpa only [pointPrefix_full] using pointPrefix_lt q q.parameters.n
  exact NearCubicGates.Close.Dispatch.natBitLength_le_of_lt
    (hp.trans_le (Nat.pow_le_pow_right (by decide) (by omega : q.parameters.n ≤ q.parameters.n + 1)))
    (by omega)

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: all five actual population-request
fields have binary length bounded by the finite original Entry source. -/
theorem populationInputFields_bits {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    ∀ p ∈ populationInputFields r, natBitLength p.2 ≤ (entryWord r).length + 1 := by
  have hs := entrySource_lengths r
  have hk : natBitLength r.selected.1.k ≤ (entryWord r).length :=
    (parameter_bitLength_le_word r.selected.1 _ (by simp [parameterHeadFields, parameterHeadScalars])).trans hs.2.2.2.1
  have hcorner (left right : Bool) :
      natBitLength (entryPointRequest r left right).packed ≤ (entryWord r).length + 1 :=
    (pointPacked_bits (entryPointRequest r left right)).trans (Nat.add_le_add_right hs.2.2.2.2 1)
  have hc : ∀ i : Fin 4, natBitLength (entryCorners r i) ≤ (entryWord r).length + 1 := by
    intro i
    fin_cases i
    · exact hcorner false false
    · exact hcorner true false
    · exact hcorner false true
    · exact hcorner true true
  intro p hp
  simp only [populationInputFields, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hk.trans (Nat.le_succ _)
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc 3

/-- `def:mask` and `prop:time`, paper/paper.tex: even uncertified original four-corner populations
are at most twice the retained original occurrence horizon. -/
theorem entryPopulation_value_le {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPopulationRequest r).value ≤ 2 * (entryWord r).length := by
  have hp := StageCert.populationPrefix_le (r.call.first.gates ++ r.call.second.gates)
    (entryCorners r) (Program.witnessPrefix r.call r.selected.1 r.witness) r.selected.1.k
    (r.call.first.gates.length + r.call.second.gates.length)
  have hs := entrySelection_fits r
  have hw := (entrySource_lengths r).2.2.1
  change (entryPopulationRequest r).value ≤ _ at hp
  omega

/-- `prop:time`, paper/paper.tex: the complete
actual selected population reply has binary length bounded linearly
by the finite original numeric-entry word. -/
theorem entryPopulation_bits {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    natBitLength (entryPopulationRequest r).value ≤ 2 * (entryWord r).length + 1 :=
  (NearCubicGates.Close.Dispatch.natBitLength_le_succ _).trans
    (Nat.add_le_add_right (entryPopulation_value_le r) 1)

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: all three literal subroutine source
words have linear size in the actual finite original Entry source. -/
theorem entryRequest_words {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (structuralWord (entryStructuralRequest r)).length ≤ 20 * ((entryWord r).length + 2) ∧
    (entryPopulationRequest r).word.length ≤ 20 * ((entryWord r).length + 2) ∧
    (entryPredicateRequest r).word.length ≤ 20 * ((entryWord r).length + 2) := by
  have hs := entrySource_lengths r
  have hstr := structuralWord_length (entryStructuralRequest r)
  have hfields := populationInputFields_bits r
  have hp0 := hfields (38, r.selected.1.k) (by simp [populationInputFields])
  have hp1 := hfields (114, entryCorners r 0) (by simp [populationInputFields])
  have hp2 := hfields (115, entryCorners r 1) (by simp [populationInputFields])
  have hp3 := hfields (116, entryCorners r 2) (by simp [populationInputFields])
  have hp4 := hfields (117, entryCorners r 3) (by simp [populationInputFields])
  dsimp only [Prod.snd] at hp0 hp1 hp2 hp3 hp4
  have hpoint := pointPacked_bits (entryPointRequest r true true)
  change natBitLength (entryPredicateRequest r).point ≤ r.call.n + 1 at hpoint
  constructor
  · change _ ≤ 5 * (Program.prepWord B1 B2 r.call r.witness).length + 2 at hstr
    omega
  constructor
  · change ((callWord r.call) ++ natWord r.selected.1.k ++
      (List.ofFn (entryCorners r)).flatMap natWord ++
      frame (Program.witnessPrefix r.call r.selected.1 r.witness)).length ≤ _
    rw [List.append_assoc (callWord r.call), ← populationInputFields_word]
    simp only [populationInputFields, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, NearCubicGates.Close.Dispatch.natWord_length, frame_length]
    omega
  · change (natWord (entryPredicateRequest r).point ++ callWord r.call).length ≤ _
    simp only [List.length_append, NearCubicGates.Close.Dispatch.natWord_length]
    omega

end NearQuarticWires.StageMainMask
