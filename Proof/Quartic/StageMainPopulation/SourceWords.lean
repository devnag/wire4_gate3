import Proof.Quartic.StageMainPopulation.Request

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

def sourceTail (r : PopulationRequest) : List Bool :=
  listWord natWord r.call.parity ++ ratWord r.call.radius ++ metadataWord r ++ frame r.witness

def firstListRest (r : PopulationRequest) : List Bool :=
  listWord NearCubicGates.Close.Interfaces.intWord r.call.first.coeffs ++ listWord bitWord r.call.first.table ++
    (circuitWord r.call.second ++ sourceTail r)

def secondListRest (r : PopulationRequest) : List Bool :=
  listWord NearCubicGates.Close.Interfaces.intWord r.call.second.coeffs ++ listWord bitWord r.call.second.table ++ sourceTail r

/-- `def:class` and `def:mask`, paper/paper.tex: both complete original circuits precede the binary metadata
and the actual framed selection witness in the literal input. -/
theorem source_shape (r : PopulationRequest) :
    r.word = (natWord r.call.n ++ natWord (kindTag r.call.kind)) ++
      (circuitWord r.call.first ++ (circuitWord r.call.second ++ sourceTail r)) := by
  rw [request_word]
  simp only [witnessPrefix, callWord, sourceTail, List.append_assoc]

theorem firstCircuit_input (r : PopulationRequest) :
    r.word.drop (pos1 r.call) = circuitWord r.call.first ++
      (circuitWord r.call.second ++ sourceTail r) := by
  rw [source_shape, show pos1 r.call =
    (natWord r.call.n ++ natWord (kindTag r.call.kind)).length by
      simp only [pos1, List.length_append]]
  exact List.drop_left

theorem firstList_input (r : PopulationRequest) :
    r.word.drop (pos1 r.call) = listWord gateWord r.call.first.gates ++ firstListRest r := by
  simpa only [circuitWord, firstListRest, List.append_assoc] using firstCircuit_input r

theorem secondCircuit_input (r : PopulationRequest) :
    r.word.drop (pos2 r.call) = circuitWord r.call.second ++ sourceTail r := by
  unfold pos2
  rw [← List.drop_drop, firstCircuit_input, List.drop_left]

theorem secondList_input (r : PopulationRequest) :
    r.word.drop (pos2 r.call) = listWord gateWord r.call.second.gates ++ secondListRest r := by
  simpa only [circuitWord, secondListRest, List.append_assoc] using secondCircuit_input r

/-- `prop:time`, paper/paper.tex: the actual
witness supplies every selected occurrence index in both original banks. -/
theorem counts_le (r : PopulationRequest) :
    r.call.first.gates.length + r.call.second.gates.length ≤ r.word.length := by
  have h := r.selection_fits
  have h' := (encoding_bounds r).2.2.1
  omega

theorem corner_bitLength (r : PopulationRequest) (l : Fin 4) :
    natBitLength (r.corners l) ≤ r.word.length := by
  apply (encoding_bounds r).2.2.2 (cornerPoint l, r.corners l)
  fin_cases l <;> simp only [metadataFields, List.mem_cons, List.not_mem_nil, or_false] <;> tauto

/-- `sec:cells` and `def:mask`, paper/paper.tex: arbitrary four point codes allow magnitudes of two,
and the complete original-bank population remains source-count bounded. -/
theorem value_le (r : PopulationRequest) :
    r.value ≤ 2 * (r.call.first.gates.length + r.call.second.gates.length) :=
  populationPrefix_le _ _ _ _ _

end NearQuarticWires.StageMainPopulation
