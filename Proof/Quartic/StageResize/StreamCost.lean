import Proof.Quartic.StageResize.StreamWordFunction

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CellsPack (Gof)

theorem StreamResizeRequest.word_length (r : StreamResizeRequest) :
    r.word.length = 2 * natBitLength r.outputWidth +
      (2 * r.inputWidth + 1) * r.fieldCount + 2 := by
  unfold StreamResizeRequest.word
  rw [fieldsRecs_eq_numberRecords]
  simp only [List.length_append, Pool.natWord_eq, List.length_replicate,
    List.length_cons, List.length_nil, numberRecords_length,
    NearCubicWires.RepairOrdinary.SignedSortKey.binary_length,
    List.length_map, StreamResizeRequest.fieldCount]
  omega

/-- `prop:time`, paper/paper.tex: each source
field contributes its actual fixed-width record exactly once. -/
theorem StreamResizeRequest.word_length_le (r : StreamResizeRequest) :
    r.word.length ≤ 6 * (r.fieldCount + 1) * (r.inputWidth + r.outputWidth + 1) := by
  rw [r.word_length]
  have h := bitLength_le r.outputWidth
  nlinarith

/-- `prop:time`, paper/paper.tex: one executed
marker-controlled iteration per field gives linear field-count cost. -/
theorem streamSourceClock_le (r : StreamResizeRequest) :
    streamSourceClock r ≤
      200 * (r.fieldCount + 1) * (r.inputWidth + r.outputWidth + 1) := by
  have h := bitLength_le r.outputWidth
  unfold streamSourceClock streamBodyClock streamLoopClock
  nlinarith

theorem stream_setup_width_le (r : StreamResizeRequest) :
    resizeSizes.W (leadOnes r.word) ≤ 128 * (r.outputWidth + 1) := by
  simp only [resizeSizes, Sz.W, one_mul, stream_input_leadOnes, natBitLength, pow_succ]
  have h := Nat.pow_log_le_add_one 2 r.outputWidth
  omega

/-- `prop:time`, paper/paper.tex: the structural
compiler cost retains a single factor of the source field census. -/
theorem scalar_stream_compiler_bound (A V count : ℕ) (hA : 1 ≤ A) :
    10 ^ 6 * ((201 * count * V) * (A * V) ^ 2) + 60 * count * V ≤
      10 ^ 12 * A ^ 2 * count * V ^ 3 := by
  have hv3 : V ≤ V ^ 3 := Nat.le_self_pow (by decide) V
  have ha2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  have hsmall : 60 * count * V ≤ 60 * A ^ 2 * count * V ^ 3 := by
    have hh : V ≤ A ^ 2 * V ^ 3 := hv3.trans (Nat.le_mul_of_pos_left _ ha2)
    have hh' := Nat.mul_le_mul_left (60 * count) hh
    nlinarith only [hh']
  have he : 10 ^ 6 * ((201 * count * V) * (A * V) ^ 2) =
      201000000 * A ^ 2 * count * V ^ 3 := by ring
  rw [he]
  nlinarith only [hsmall]

/-- `prop:time`, paper/paper.tex: actual cold
ordinary stream resizing is linear in field count and cubic in widths;
there is no extra child-choice or squared census factor. -/
theorem StreamResizeRequest.budget_polynomial (r : StreamResizeRequest) :
    r.budget ≤ resizeCostConstant * (r.fieldCount + 1) *
      (r.inputWidth + r.outputWidth + 1) ^ 3 := by
  let V := r.inputWidth + r.outputWidth + 1
  let count := r.fieldCount + 1
  let A := TSK resizeCallee + 300
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hc : 1 ≤ count := by dsimp [count]; omega
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hL : leadOnes r.word ≤ V := by
    rw [stream_input_leadOnes]
    have hh := bitLength_le r.outputWidth
    dsimp [V]
    omega
  have hW : resizeSizes.W (leadOnes r.word) ≤ 128 * V := by
    exact (stream_setup_width_le r).trans (Nat.mul_le_mul_left _ (by dsimp [V]; omega))
  have hG : Gof resizeCallee resizeSizes (leadOnes r.word) ≤ A * V := by
    simp only [Gof, Sz.Lk, Sz.Bk, resizeSizes, Nat.zero_mul, pow_zero, mul_zero, add_zero]
    change resizeSizes.W (leadOnes r.word) + leadOnes r.word + 64 + 1 +
      TSK resizeCallee + 1 ≤ A * V
    exact scalar_setup_bound hW hL hV
  have hN : streamSourceClock r + 1 ≤ 201 * count * V := by
    have hh := streamSourceClock_le r
    change streamSourceClock r ≤ 200 * count * V at hh
    have hp : 1 ≤ count * V := Nat.mul_pos hc hV
    nlinarith
  have hi : 10 * r.word.length ≤ 60 * count * V := by
    have hh := Nat.mul_le_mul_left 10 r.word_length_le
    change 10 * r.word.length ≤ 10 * (6 * count * V) at hh
    nlinarith only [hh]
  have h := NearCubicGates.Close.CellsPack.lang_le2 resizeCallee resizeSizes r.word (streamSourceClock r)
  calc
    r.budget ≤ 10 ^ 6 * ((streamSourceClock r + 1) *
      Gof resizeCallee resizeSizes (leadOnes r.word) ^ 2) + 10 * r.word.length := h
    _ ≤ 10 ^ 6 * ((201 * count * V) * (A * V) ^ 2) + 60 * count * V :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul hN (Nat.pow_le_pow_left hG 2))) hi
    _ ≤ 10 ^ 12 * A ^ 2 * count * V ^ 3 := scalar_stream_compiler_bound A V count hA
    _ = resizeCostConstant * (r.fieldCount + 1) *
      (r.inputWidth + r.outputWidth + 1) ^ 3 := rfl

end NearQuarticWires.StageResize
