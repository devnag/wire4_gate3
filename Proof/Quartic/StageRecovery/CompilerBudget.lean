import Proof.Quartic.StageRecovery.CompilerClock

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: a genuine binary
Cells compilation with a linear-in-hint source clock has a cubic-in-hint
physical budget, preserving a separately supplied quadratic census. -/
theorem pointLangBudget_le (inp : List Bool) (steps A H : ℕ)
    (hA : 1 ≤ A) (hH : 1 ≤ H) (hL : leadOnes inp ≤ H)
    (hW : 2 ^ leadOnes inp * 64 ≤ 128 * H)
    (hsteps : steps ≤ 10 ^ 6 * A ^ 2 * H)
    (hin : inp.length ≤ 100 * A * H) :
    langBudget packetCallee pointSizes VV MM inp steps ≤
      10 ^ 16 * (TSK packetCallee + 10) * A ^ 2 * H ^ 3 := by
  let L := leadOnes inp
  let W := 2 ^ L * 64
  let F := A ^ 2 * H ^ 3
  have hl : L ≤ H := hL
  have hw : W ≤ 128 * H := hW
  have hFpos : 1 ≤ F := by
    have hp : 0 < F := by dsimp [F]; positivity
    omega
  have hH3 : H ≤ H ^ 3 := Nat.le_self_pow (by norm_num) _
  have hH2 : H ^ 2 ≤ H ^ 3 := Nat.pow_le_pow_right hH (by omega)
  have hF3 : H ^ 3 ≤ F := Nat.le_mul_of_pos_left _ (by positivity)
  have hHF := hH3.trans hF3
  have hH2F := hH2.trans hF3
  have hA2 : A ≤ A ^ 2 := Nat.le_self_pow (by norm_num) _
  have hAH : A * H ≤ F := Nat.mul_le_mul hA2 hH3
  have hLF : L ≤ F := hl.trans hHF
  have hWF : W ≤ 128 * F := hw.trans (Nat.mul_le_mul_left _ hHF)
  have hLW : L * W ≤ 128 * F := by
    calc L * W ≤ H * (128 * H) := Nat.mul_le_mul hl hw
      _ = 128 * H ^ 2 := by ring
      _ ≤ 128 * F := Nat.mul_le_mul_left _ hH2F
  have hi : inp.length ≤ 100 * F := hin.trans (by nlinarith [hAH])
  have hn : steps ≤ 10 ^ 6 * F := by
    calc steps ≤ 10 ^ 6 * A ^ 2 * H := hsteps
      _ ≤ 10 ^ 6 * A ^ 2 * H ^ 3 := Nat.mul_le_mul_left _ hH3
      _ = _ := by dsimp [F]; ring
  have hw1 : W + 1 ≤ 129 * H := by omega
  have hnw : steps * (W + 1) ≤ 10 ^ 6 * 129 * F := by
    calc steps * (W + 1) ≤ (10 ^ 6 * A ^ 2 * H) * (129 * H) :=
        Nat.mul_le_mul hsteps hw1
      _ = (10 ^ 6 * 129 * A ^ 2) * H ^ 2 := by ring
      _ ≤ (10 ^ 6 * 129 * A ^ 2) * H ^ 3 := Nat.mul_le_mul_left _ hH2
      _ = _ := by dsimp [F]; ring
  have hnw2 : steps * (W + 1) ^ 2 ≤ 10 ^ 6 * 129 ^ 2 * F := by
    calc steps * (W + 1) ^ 2 ≤ (10 ^ 6 * A ^ 2 * H) * (129 * H) ^ 2 :=
        Nat.mul_le_mul hsteps (Nat.pow_le_pow_left hw1 _)
      _ = _ := by dsimp [F]; ring
  have hnt : steps * (TSK packetCallee + 3) ≤
      10 ^ 6 * F * (TSK packetCallee + 10) :=
    Nat.mul_le_mul hn (by omega)
  have hFT : F ≤ (TSK packetCallee + 10) * F := Nat.le_mul_of_pos_left _ (by omega)
  rw [show 10 ^ 16 * (TSK packetCallee + 10) * A ^ 2 * H ^ 3 =
    10 ^ 16 * (TSK packetCallee + 10) * F by dsimp [F]; ring]
  unfold langBudget
  simp only [pointSizes, Sz.W, Sz.Lk, Sz.Bk, Nat.one_mul, Nat.zero_mul,
    Nat.pow_zero, Nat.mul_zero]
  change (costA pointSizes L + 1 + (costB VV MM W 0 0 + 1 + costC L W 0 0)) + 1 +
    (steps * (500 * (W + 1) ^ 2 + 100 * (TSK packetCallee + 3)) + 1 +
      (10 * inp.length + 5 * steps + 5 * (0 + 3) +
        MM * (5 * ((2 * W + 1) * steps) + 2) + 10)) ≤ _
  simp only [costA, costB, costC, pointSizes, Sz.W, Sz.Lk, Sz.Bk,
    Nat.one_mul, Nat.zero_mul, Nat.pow_zero, Nat.mul_zero, Nat.mul_one, VV, MM]
  change (30 * L + 20 + 256 + (L * (60 * W + 11 + 8) + 7 * L + 3) +
    0 + (L * (0 + 0 + 8) + 7 * L + 3) + 0 + (L * (0 + 0 + 8) + 7 * L + 3) +
    (0 + 3) + (0 + 3) + (0 + 3) + 4 * 3 + 10 + 1 +
    ((128 + 2) * (50 * W + 10 + 1) + 10 * (1 + 1) + (0 + 10) +
      (40 * (0 + 0 + 0 + 3) + 10) + 3 + 1 +
      ((3 * L + 1) + (3 * W + 1) + (0 + 1) + (0 + 1) +
        (3 * (0 + 0 + 0 + 3) + 1) + 4))) + 1 +
    (steps * (500 * (W + 1) ^ 2 + 100 * (TSK packetCallee + 3)) + 1 +
      (10 * inp.length + 5 * steps + 15 +
        10 * (5 * ((2 * W + 1) * steps) + 2) + 10)) ≤ _
  nlinarith

/-- `prop:time`, paper/paper.tex: the actual original
Formula request contains only its seven literal header fields and the
unchanged original token bytes, with no generated-family duplication. -/
theorem FamilyCompileRequest.word_length_le (r : FamilyCompileRequest) :
    r.word.length ≤ 50 * (r.setupHint + 1) := by
  have hfields : (r.header.flatMap NearCubicWires.RepairRepresentation.natWord).length ≤
      7 * (2 * (r.setupHint + 2) + 1) := by
    rw [List.length_flatMap]
    calc (r.header.map fun v => (NearCubicWires.RepairRepresentation.natWord v).length).sum ≤
        (r.header.map fun _ => 2 * (r.setupHint + 2) + 1).sum := by
          apply List.sum_le_sum
          intro v hv
          rw [NearCubicGates.Close.Cells.natWord_length]
          have h := r.header_bits v hv
          omega
      _ = _ := by
        have hlen : r.header.length = 7 := rfl
        simp [hlen]
        ring
  have hL := r.token_length_le
  have hh := r.clock_dimensions.2.2.1
  rw [r.word_eq_header, List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: retaining the
original Formula once and appending the actual family packet has a
linear family-count input size, with its terminal delimiter charged. -/
theorem FamilyCompileRequest.cacheInput_length_le (r : FamilyCompileRequest) :
    r.cacheInput.length ≤
      100 * ((famPairs r.source.arity r.degree).length + 1) * (r.setupHint + 1) := by
  have hs := r.word_length_le
  have hw := r.clock_dimensions.2.2.2.2
  have hfamily : r.family.output.length =
      (famPairs r.source.arity r.degree).length * (2 * r.family.width + 1) + 1 := by
    change (nativeFamilyPacket r.family.width (famRecs r.source.arity r.degree)).length = _
    rw [nativeFamilyPacket_length, famRecs_eq, List.length_map]
  have hprod := Nat.mul_le_mul_left (famPairs r.source.arity r.degree).length hw
  unfold FamilyCompileRequest.cacheInput
  rw [List.length_append, hfamily]
  nlinarith

end NearQuarticWires.StageRecovery
