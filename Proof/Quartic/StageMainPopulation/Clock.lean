import Proof.Quartic.StageMainPopulation.Program

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairRepresentation
open StageMainMask

/-- `prop:time`, paper/paper.tex: all literal
source parsing, original-bank scans, top traversal and binary output
have one fixed polynomial bound in the actual input word length. -/
theorem rawSteps_le (r : PopulationRequest) :
    rawSteps r r.word.length ≤ 10000 * (r.word.length + 2)^4 := by
  let L := r.word.length
  let V := L + 2
  have hc := counts_le r
  change r.call.first.gates.length + r.call.second.gates.length ≤ L at hc
  have hm : (metadataWord r).length ≤ L := by
    have h := congrArg List.length (request_word r)
    simp only [witnessPrefix, List.length_append] at h
    dsimp [L]
    omega
  have hmeta : StageOutput.readScalarsCost (metadataFields r) ≤ 40 * L + 1 := by
    have hread := StageOutput.readScalarsCost_le_word (metadataFields r)
    change StageOutput.readScalarsCost (metadataFields r) ≤ 40 * (metadataWord r).length + 1 at hread
    omega
  have hlog1 : natBitLength r.call.first.gates.length ≤ r.call.first.gates.length + 1 := by
    unfold natBitLength
    have h := Nat.log_le_self 2 r.call.first.gates.length
    omega
  have hlog2 : natBitLength r.call.second.gates.length ≤ r.call.second.gates.length + 1 := by
    unfold natBitLength
    have h := Nat.log_le_self 2 r.call.second.gates.length
    omega
  have hv := value_le r
  have hlogv : natBitLength r.value ≤ 2 * L + 1 := by
    unfold natBitLength
    have h := Nat.log_le_self 2 r.value
    omega
  have hmain :
      (r.call.first.gates.length + r.call.second.gates.length) * (900 * V^2 + 106) ≤
        900 * V^3 + 106 * V := by
    calc
      _ ≤ V * (900 * V^2 + 106) := Nat.mul_le_mul_right _ (by dsimp [V]; omega)
      _ = _ := by ring
  have hp1 : V ≤ V^4 := Nat.le_self_pow (by decide : (4 : ℕ) ≠ 0) V
  have hp3 : V^3 ≤ V^4 := Nat.pow_le_pow_right (by dsimp [V]; omega) (by decide)
  have hp0 : 1 ≤ V^4 := Nat.one_le_pow _ _ (by dsimp [V]; omega)
  change rawSteps r L ≤ 10000 * V^4
  unfold rawSteps acquireSteps replaySteps bankSteps
  change 3000 * V^3 + _ + 100 * V + 20 +
    (r.call.first.gates.length * (900 * V^2 + 106) + 30 * natBitLength r.call.first.gates.length + 37) +
    (800 * V^3 + 5 * L + 20) +
    (r.call.second.gates.length * (900 * V^2 + 106) + 30 * natBitLength r.call.second.gates.length + 37) +
    40 * natBitLength r.value + 100 ≤ _
  have hL : L ≤ V := by dsimp [V]; omega
  nlinarith only [hmain, hmeta, hlog1, hlog2, hlogv, hc, hp1, hp3, hp0, hL]

end NearQuarticWires.StageMainPopulation
