import Proof.Quartic.StageModularCuts.Stream

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: each actual signed
cut occupies at least one source cell. -/
theorem cuts_count_le_stream (p : ℕ) (cuts : List MatrixScoreBatch.Cut) :
    cuts.length ≤ (cuts.flatMap (MatrixScoreBatch.cutWord p)).length := by
  induction cuts with
  | nil => simp
  | cons c cs ih =>
    have hc : 1 ≤ (MatrixScoreBatch.cutWord p c).length := by
      rw [cutWord_length]
      nlinarith
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

/-- `prop:time`, paper/paper.tex: the fixed binary
row computation is quadratic in the dense and signed-field widths. -/
theorem rowCost_bound (p w S : ℕ) (hp : p ≤ S) (hw : w ≤ S) :
    rowCost p w + 2 ≤ 10000 * (S + 1) ^ 2 := by
  have hm : rowCost p w ≤ rowCost S S := by
    unfold rowCost transferCost coefficientCost BinW.divCost
    gcongr
  have hb : rowCost S S + 2 ≤ 10000 * (S + 1) ^ 2 := by
    unfold rowCost transferCost coefficientCost BinW.divCost
    nlinarith
  omega

/-- `prop:time`, paper/paper.tex: the complete
actual cut stream is processed in linear stream length times a fixed
polynomial in widths, with no whole-stream square. -/
theorem streamCost_bound (r : Setup.Request) :
    streamCost r ≤ 50000 * (Setup.scale r) ^ 2 * (r.stream.length + 1) := by
  obtain ⟨hs, hw⟩ := setup_scale_bounds r
  have hr := rowCost_bound r.fieldWidth r.width (Setup.scale r) (by omega) (by omega)
  have hq : (Setup.scale r + 1) ^ 2 ≤ 4 * (Setup.scale r) ^ 2 := by nlinarith
  have hrow : rowCost r.fieldWidth r.width + 2 ≤ 40000 * (Setup.scale r) ^ 2 := by omega
  have hc : r.cuts.length ≤ r.stream.length := cuts_count_le_stream r.fieldWidth r.cuts
  have hm := Nat.mul_le_mul hc hrow
  change r.cuts.length * (rowCost r.fieldWidth r.width + 2) + 9 ≤ _
  nlinarith

/-- `prop:time`, paper/paper.tex: the real eleven-field
loader's clock is affine in actual source bits and the unary widths. -/
theorem setup_loadCost_eq (r : Setup.Request) :
    Setup.loadCost r = 12 * (r.stream.length + r.fieldWidth + r.width +
      2 * natBitLength r.modulus + 1) + 93 := by
  simp only [Setup.loadCost, Top.loadCost, Top.loadRec, Top.loadChainCost,
    List.length_append, frame_length, List.length_replicate, List.length_nil,
    NearCubicGates.Close.CounterAsm.natWord_len]
  ring

/-- `prop:time`, paper/paper.tex: the cold loader
uses only binary modulus length and linear raw-cut stream work. -/
theorem setup_loadCost_bound (r : Setup.Request) :
    Setup.loadCost r ≤ 100 * Setup.scale r * (r.stream.length + 1) := by
  rw [setup_loadCost_eq]
  have hs := (setup_scale_bounds r).1
  have hsum : r.fieldWidth + r.width + 2 * natBitLength r.modulus + 1 ≤ 2 * Setup.scale r := by
    unfold Setup.scale
    omega
  nlinarith

/-- `prop:time`, paper/paper.tex: the combined cold
setup, linear row pass, outer framing, and ordinary head reset fit the
literal downstream printer budget for every actual request. -/
theorem full_clock_bound (r : Setup.Request) :
    2 * (Setup.clock r + 1 + streamCost r) + 2 ≤
      10 ^ 30 * (Setup.scale r) ^ 20 * (r.stream.length + 1) := by
  have hs := (setup_scale_bounds r).1
  have hload := setup_loadCost_bound r
  have hstream := streamCost_bound r
  have h1 : Setup.scale r ≤ (Setup.scale r) ^ 20 := Nat.le_self_pow (by decide) _
  have h2 : (Setup.scale r) ^ 2 ≤ (Setup.scale r) ^ 20 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : (Setup.scale r) ^ 4 ≤ (Setup.scale r) ^ 20 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have ht : 0 < (Setup.scale r) ^ 20 * (r.stream.length + 1) :=
    Nat.mul_pos (pow_pos (by omega : 0 < Setup.scale r) _) (by omega)
  have hl' : Setup.loadCost r ≤ 100 * (Setup.scale r) ^ 20 * (r.stream.length + 1) :=
    hload.trans (by gcongr)
  have hs' : streamCost r ≤ 50000 * (Setup.scale r) ^ 20 * (r.stream.length + 1) :=
    hstream.trans (by gcongr)
  have hp : 10 ^ 6 * (Setup.scale r) ^ 4 ≤
      10 ^ 6 * (Setup.scale r) ^ 20 * (r.stream.length + 1) := by
    calc
      _ ≤ 10 ^ 6 * (Setup.scale r) ^ 20 := by gcongr
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  unfold Setup.clock
  simp only [Nat.mul_assoc] at hl' hs' hp ht ⊢
  omega

end NearQuarticWires.StageModularCuts
