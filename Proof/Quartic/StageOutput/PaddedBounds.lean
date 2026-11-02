import Proof.Quartic.StageOutput.Prepare
import Proof.Quartic.StageOutput.Semantics

/-!
# Binary capacity supplied by the explicit padding

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The second arithmetic pass uses the physically written
padded word. Its length bounds `n` and every scalar bit length; the allocated
fourth-power width therefore supplies the fixed arithmetic headroom.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch

theorem Input.padded_length (d : Input) : d.padded.length = d.word.length + d.n + 1 := by
  simp [Input.padded]

theorem Input.field_capacity (d : Input) : ∀ xv ∈ d.fields, xv.2 < 2 ^ d.padded.length := by
  intro xv hx
  have hlen := fieldWord_length d.fields xv hx
  rw [natWord_length] at hlen
  change 2 * natBitLength xv.2 + 1 ≤ d.word.length at hlen
  have hv := lt_natBitLength xv.2
  exact hv.trans_le (Nat.pow_le_pow_right (by norm_num) (by rw [d.padded_length]; omega))

theorem padded_width (L : ℕ) : 64 * (L + 1) ≤ wdOf 4 L := by
  have hc : 64 ≤ (L + 4) ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (L + 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hh := Nat.mul_le_mul_right (L + 4) hc
  rw [← pow_succ] at hh
  norm_num only [Nat.reduceAdd] at hh
  unfold wdOf
  omega

theorem padded_word_length_le_width (L : ℕ) : L + 2 ≤ wdOf 4 L := by
  have := padded_width L
  omega

theorem padded_word_capacity (L : ℕ) : L + 2 < 2 ^ wdOf 4 L :=
  (padded_word_length_le_width L).trans_lt Nat.lt_two_pow_self

end NearQuarticWires.StageOutput
