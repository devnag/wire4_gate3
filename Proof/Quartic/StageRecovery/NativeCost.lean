import Proof.Quartic.StageRecovery.NativeRecovery
import Proof.Quartic.StagePrint.FullTableBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the actual
hint and two source codecs have length bounded by their real bit-width
hint, including a target count no larger than the native census. -/
theorem NativeRequest.header_length_le (r : NativeRequest) :
    r.header.length ≤ 10 * (r.packet.hint + 1) := by
  have hc := r.prefix.count_bits
  change natBitLength r.targetCount ≤ natBitLength (tableNaturals r.table).length at hc
  rw [tableNaturals_length] at hc
  have he := r.nativeHint_eq
  unfold NativeRequest.nativeHint at he
  have hh := nbl_le_self r.packet.hint
  simp only [NativeRequest.header, List.length_append, natWord_length]
  omega

/-- `prop:time`, paper/paper.tex: the native
machine's existing clock already pays every input byte, actual native
column and dimension-extraction operation. -/
theorem NativeRequest.native_lower_bounds (a : WilliamsAlgorithm) (r : NativeRequest) :
    r.table.loadCost ≤ StagePrint.fullTableCost a r.table ∧
    r.table.word.length ≤ StagePrint.fullTableCost a r.table ∧
    r.table.count + 1 ≤ StagePrint.fullTableCost a r.table := by
  have hl : r.table.word.length ≤ r.table.loadCost := by
    unfold StagePrint.TableRequest.loadCost Top.loadCost
    change r.table.word.length ≤ 2 * (2 * r.table.word.length + 1) + 2 + 1 + _
    omega
  unfold StagePrint.fullTableCost
  omega

/-- `prop:time`, paper/paper.tex: the complete
native packet length, including padding, is at most its actual native
census times a fixed linear bit-width factor. -/
theorem NativeRequest.native_output_length_le (r : NativeRequest) :
    r.table.output.length ≤ 10 * (r.table.count + 1) * (r.packet.hint + 1) := by
  have hs := tablePacket_stream r.table r.modulus r.modulus_pos r.nonnegative
  have hl : r.table.output.length ≤ r.packet.word.length := by
    unfold PacketRequest.word
    rw [show packetStream r.packet.width r.packet.values = r.table.output from hs]
    simp only [List.length_append]
    omega
  have hb := r.packet.word_length_le
  rw [show r.packet.values.length = r.table.count from tableNaturals_length r.table] at hb
  exact hl.trans hb

/-- `prop:time`, paper/paper.tex: outer physical
field loading and the literal outer input are linear in the actual
native input and the three real header codecs. -/
theorem NativeRequest.outer_size_cost_le (r : NativeRequest) :
    r.word.length ≤ 200 * (r.table.word.length + r.header.length + 1) ∧
    r.loadCost ≤ 200 * (r.table.word.length + r.header.length + 1) := by
  simp only [NativeRequest.word, NativeRequest.loadCost, NativeRequest.header,
    Top.loadCost, Top.loadChainCost, Top.loadRec, frame_length,
    List.length_append, List.length_nil]
  omega

/-- `prop:time`, paper/paper.tex: the actual
cold header clock is bounded by the existing native clock and a fixed
quadratic polynomial in the small decoder bit-width hint. -/
theorem NativeRequest.headerBudget_le (a : WilliamsAlgorithm) (r : NativeRequest) :
    r.headerBudget ≤ 10 ^ 6 * (StagePrint.fullTableCost a r.table + 1) * (r.packet.hint + 1) ^ 2 := by
  let T := StagePrint.fullTableCost a r.table + 1
  let H := r.packet.hint + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have he := r.nativeHint_eq
  unfold NativeRequest.nativeHint at he
  have hq : r.table.q ≤ H := by dsimp [H]; omega
  have hm : natBitLength r.modulus ≤ H := by dsimp [H]; omega
  have hn : natBitLength r.table.count ≤ H := by dsimp [H]; omega
  have hh : natBitLength r.packet.hint ≤ H := nbl_le_self _
  have hl := r.header_length_le
  change r.header.length ≤ 10 * H at hl
  have hb := r.native_lower_bounds a
  have hcount : r.table.count ≤ T := by dsimp [T]; omega
  have hload : r.table.loadCost ≤ T := by dsimp [T]; omega
  have hword : r.table.word.length ≤ T := by dsimp [T]; omega
  have ho := r.outer_size_cost_le
  have hout : r.loadCost ≤ 5000 * T * H := by
    have hp := Nat.mul_le_mul hT hH
    nlinarith [ho.2, Nat.mul_le_mul_left T hH, Nat.mul_le_mul_left H hT]
  have hM : (natWord r.modulus).length ≤ r.header.length := by
    simp only [NativeRequest.header, List.length_append]; omega
  have hN : (natWord r.targetCount).length ≤ r.header.length := by
    simp only [NativeRequest.header, List.length_append]; omega
  have hw : (natBitLength r.packet.hint + 10) * (100 * r.packet.hint + 200) ≤ 3300 * H ^ 2 := by
    have h1 : natBitLength r.packet.hint + 10 ≤ 11 * H := by omega
    have h2 : 100 * r.packet.hint + 200 ≤ 300 * H := by dsimp [H]; omega
    exact (Nat.mul_le_mul h1 h2).trans_eq (by ring)
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hTH := Nat.mul_le_mul_left T hH2
  have h1TH := Nat.mul_le_mul_right (H ^ 2) hT
  have h1T := Nat.mul_le_mul_right H hT
  change r.headerBudget ≤ 10 ^ 6 * T * H ^ 2
  unfold NativeRequest.headerBudget NativeRequest.headerSteps NativeRequest.metadataSteps
    NativeRequest.dimensionsSteps NativeRequest.hintSteps NativeRequest.headerEmitSteps
  nlinarith

end NearQuarticWires.StageRecovery
