import Proof.Quartic.StageMain.ThresholdValue
import Proof.Gates.Dispatch.ParseCirc

/-!
# Capacity bounds from a literal threshold-gate encoding

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The encoded signed coefficients bound
their absolute sum, and the coordinate count is bounded by the same word.
These bounds reserve enough binary cells for the two score accumulators.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

theorem gateWord_eq {n : ℕ} (g : NormalizedThresholdGate n) :
    gateWord g = natWord n ++ ((List.ofFn g.weight).flatMap NearCubicGates.Close.Interfaces.intWord ++ NearCubicGates.Close.Interfaces.intWord g.threshold) := by
  simp [gateWord, listWord, List.append_assoc]

theorem gate_encoding_bounds {n : ℕ} (g : NormalizedThresholdGate n) :
    n ≤ (gateWord g).length ∧ natBitLength n ≤ (gateWord g).length ∧
    (List.ofFn g.weight |>.map Int.natAbs).sum + g.threshold.natAbs < 2 ^ (gateWord g).length := by
  have hn := length_le_flatMap (List.ofFn g.weight) NearCubicGates.Close.Interfaces.intWord intWord_len_pos
  have hb := natBitLength_le_len n
  have hs := sum_natAbs_lt (List.ofFn g.weight ++ [g.threshold])
  simp only [List.length_ofFn] at hn
  simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.length_append] at hs
  rw [gateWord_eq, List.length_append, List.length_append]
  refine ⟨by omega, by omega, hs.trans_le ?_⟩
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem gate_score_capacity {n : ℕ} (g : NormalizedThresholdGate n) {L W : ℕ}
    (hL : (gateWord g).length ≤ L) (hW : L + 3 ≤ W) :
    3 * (List.ofFn g.weight |>.map Int.natAbs).sum + g.threshold.natAbs + 1 < 2 ^ W := by
  have hs := (gate_encoding_bounds g).2.2
  have hpow : 2 ^ (gateWord g).length ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL
  have hwide : 8 * 2 ^ L ≤ 2 ^ W := by
    have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hW
    simpa [pow_add, Nat.mul_comm] using this
  have hp : 0 < 2 ^ L := by positivity
  omega

end NearQuarticWires.StageMain
