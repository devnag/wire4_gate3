import Proof.Quartic.StageRecovery.ModPointMachine
import Proof.Gates.CounterMachine.PrefixFinal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: the actual modular
point input contains only five binary fields and the original formula
token stream, with length polynomial in its structural hint. -/
theorem ModPointRequest.word_length_le (r : ModPointRequest) :
    r.word.length ≤ 50 * (r.source.hint + 1) := by
  rw [r.word_eq, List.length_append]
  have hf : (r.fields.flatMap NearCubicWires.RepairRepresentation.natWord).length ≤
      r.fields.length * (2 * (r.source.hint + 2) + 1) := by
    rw [List.length_flatMap]
    calc (r.fields.map fun value => (NearCubicWires.RepairRepresentation.natWord value).length).sum ≤
        (r.fields.map fun _ => 2 * (r.source.hint + 2) + 1).sum := by
          apply List.sum_le_sum
          intro value hv
          rw [natWord_length]
          have := r.field_bits value hv
          omega
      _ = _ := by simp
  have ht : (tokenStream (toks r.source.formula)).length ≤ 4 * (r.source.hint + 1) := by
    have h := r.source.core_width.1
    dsimp [formulaTokenBound] at h
    omega
  have hlen : r.fields.length = 5 := rfl
  rw [hlen] at hf
  omega

/-- `prop:time`, paper/paper.tex: the complete literal
postfix evaluation has a polynomial number of charged source operations
in the structural hint, independently of unreduced integer values. -/
theorem ModPointRequest.steps_le (r : ModPointRequest) :
    r.steps ≤ 10 ^ 6 * (r.source.hint + 1) ^ 2 := by
  have hf := StageGamma.readFieldsCost_le r.fields (r.source.hint + 2) r.field_bits
  have hlen : r.fields.length = 5 := rfl
  rw [hlen] at hf
  have hc := r.source.core_width.1
  have hN : (toks r.source.formula).length ≤ 4 * (r.source.hint + 1) := by
    have h := tokens_length_le_stream r.source.formula
    dsimp [formulaTokenBound] at hc
    omega
  have hB : formulaTokenBound r.source.formula + 10 ≤ 14 * (r.source.hint + 1) := by omega
  have hmul := Nat.mul_le_mul hN hB
  have hv := r.value_bits
  have hq := r.field_bits r.source.modulus (by simp [ModPointRequest.fields])
  unfold ModPointRequest.steps
  nlinarith

/-- `prop:time`, paper/paper.tex: cold binary workspace
is linear in the structural hint, rather than any value of the formula. -/
theorem ModPointRequest.context_width_le (r : ModPointRequest) :
    (ctxOf packetCallee pointSizes r.word).Wd ≤ 128 * (r.source.hint + 1) := by
  have hl : leadOnes r.word = natBitLength r.source.hint := by
    unfold ModPointRequest.word
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.source.hint
        (NearCubicWires.RepairRepresentation.natWord r.source.modulus ++
          NearCubicWires.RepairRepresentation.natWord r.point ++
            formulaWord ⟨r.source.arity, r.source.formula⟩)
  change 2 ^ (1 * leadOnes r.word) * 64 ≤ 128 * (r.source.hint + 1)
  rw [hl, Nat.one_mul]
  have := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.source.hint
  omega

/-- `prop:time`, paper/paper.tex: the actual cold
ordinary evaluator, including physical compilation and all resets, has
a fixed polynomial cost in the structural formula hint. -/
theorem ModPointRequest.budget_le (r : ModPointRequest) :
    r.budget ≤ 10 ^ 15 * (TSK packetCallee + 10) * (r.source.hint + 1) ^ 6 := by
  let H := r.source.hint + 1
  let L := leadOnes r.word
  let W := 2 ^ L * 64
  have hWeq : 2 ^ L * 64 = W := rfl
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hW : W ≤ 128 * H := by
    have h := r.context_width_le
    simpa only [ctxOf, pointSizes, Sz.W, Nat.one_mul] using h
  have hL : L ≤ H := by
    have he : leadOnes r.word = natBitLength r.source.hint := by
      unfold ModPointRequest.word
      simpa only [List.append_assoc] using
        NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.source.hint
          (NearCubicWires.RepairRepresentation.natWord r.source.modulus ++
            NearCubicWires.RepairRepresentation.natWord r.point ++ formulaWord ⟨r.source.arity, r.source.formula⟩)
    dsimp [L, H]
    rw [he]
    exact nbl_le_self _
  have hn : r.steps ≤ 10 ^ 6 * H ^ 2 := r.steps_le
  have hi : r.word.length ≤ 50 * H := r.word_length_le
  have hw1 : W + 1 ≤ 129 * H := by omega
  have hlw := Nat.mul_le_mul hL hW
  have hnw := Nat.mul_le_mul hn hw1
  have hnw2 := Nat.mul_le_mul hn (Nat.pow_le_pow_left hw1 2)
  have hnt := Nat.mul_le_mul_right (TSK packetCallee + 3) hn
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hH3 : H ^ 2 ≤ H ^ 3 := by nlinarith
  have hH4 : H ^ 3 ≤ H ^ 4 := by nlinarith
  have hH6 : H ^ 4 ≤ H ^ 6 := Nat.pow_le_pow_right hH (by omega)
  have hsmall := hH2.trans (hH3.trans (hH4.trans hH6))
  have hmiddle := hH3.trans (hH4.trans hH6)
  have hlarge := hH4.trans hH6
  have hnt6 := Nat.mul_le_mul_right (TSK packetCallee + 3) hmiddle
  change r.budget ≤ 10 ^ 15 * (TSK packetCallee + 10) * H ^ 6
  unfold ModPointRequest.budget langBudget
  simp only [pointSizes, Sz.W, Sz.Lk, Sz.Bk, Nat.one_mul, Nat.zero_mul,
    Nat.pow_zero, Nat.mul_zero]
  change (costA pointSizes L + 1 + (costB VV MM W 0 0 + 1 + costC L W 0 0)) + 1 +
    (r.steps * (500 * (W + 1) ^ 2 + 100 * (TSK packetCallee + 3)) + 1 +
      (10 * r.word.length + 5 * r.steps + 5 * (0 + 3) +
        MM * (5 * ((2 * W + 1) * r.steps) + 2) + 10)) ≤ _
  simp only [costA, costB, costC, pointSizes, Sz.W, Sz.Lk, Sz.Bk,
    Nat.one_mul, Nat.zero_mul, Nat.pow_zero, Nat.mul_zero, Nat.mul_one, VV, MM]
  rw [hWeq]
  nlinarith

end NearQuarticWires.StageRecovery
