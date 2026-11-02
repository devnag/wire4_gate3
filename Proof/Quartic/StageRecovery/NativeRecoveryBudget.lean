import Proof.Quartic.StageRecovery.NativeCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: both the
literal outer word and its fixed load have one native-clock factor and
one actual bit-width factor. -/
theorem NativeRequest.outer_word_load_bound (a : WilliamsAlgorithm) (r : NativeRequest) :
    r.word.length ≤ 5000 * (StagePrint.fullTableCost a r.table + 1) * (r.packet.hint + 1) ∧
    r.loadCost ≤ 5000 * (StagePrint.fullTableCost a r.table + 1) * (r.packet.hint + 1) := by
  let T := StagePrint.fullTableCost a r.table + 1
  let H := r.packet.hint + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hi : r.table.word.length ≤ T := (r.native_lower_bounds a).2.1.trans (by dsimp [T]; omega)
  have hh : r.header.length ≤ 10 * H := r.header_length_le
  have ho := r.outer_size_cost_le
  have h1 := Nat.mul_le_mul hT hH
  have h2 := Nat.mul_le_mul_left T hH
  have h3 := Nat.mul_le_mul_right H hT
  change r.word.length ≤ 5000 * T * H ∧ r.loadCost ≤ 5000 * T * H
  constructor <;> nlinarith [ho.1, ho.2]

/-- `prop:time`, paper/paper.tex: the published
native producer plus its real framed output scan has no additional
native-census exponent. -/
theorem nativeProducerBudget_le
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) :
    nativeProducerBudget h r ≤ 10 ^ 5 *
      (StagePrint.fullTableCost (NativeTableFrame.publishedAlgorithm h) r.table + 1) *
        (r.packet.hint + 1) := by
  let a := NativeTableFrame.publishedAlgorithm h
  let T := StagePrint.fullTableCost a r.table + 1
  let H := r.packet.hint + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : r.table.count + 1 ≤ T := (r.native_lower_bounds a).2.2.trans (by dsimp [T]; omega)
  have hout : r.table.output.length ≤ 10 * T * H :=
    r.native_output_length_le.trans (Nat.mul_le_mul_right H (Nat.mul_le_mul_left 10 hN))
  have hload : r.loadCost ≤ 5000 * T * H := (r.outer_word_load_bound a).2
  have ht1 := Nat.mul_le_mul_left T hH
  have ht2 := Nat.mul_le_mul hT hH
  have hsteps : NativeTableFrame.steps a r.table ≤ 2000 * T * H := by
    unfold NativeTableFrame.steps
    dsimp only [T] at *
    nlinarith
  change nativeProducerBudget h r ≤ 10 ^ 5 * T * H
  unfold nativeProducerBudget NativeRequest.extractorBudget
  change 4 * (2 * r.loadCost + 2) + 4 * (2 * NativeTableFrame.steps a r.table + 2) + 12 ≤ _
  nlinarith

/-- `prop:time`, paper/paper.tex: the real
header/native two-call join adds a quadratic bit-width factor while
retaining one native-clock factor and constant source copying. -/
theorem NativeRequest.joinBudget_le
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) :
    r.joinBudget h ≤ 10 ^ 8 *
      (StagePrint.fullTableCost (NativeTableFrame.publishedAlgorithm h) r.table + 1) *
        (r.packet.hint + 1) ^ 2 := by
  let a := NativeTableFrame.publishedAlgorithm h
  let T := StagePrint.fullTableCost a r.table + 1
  let H := r.packet.hint + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hhb := r.headerBudget_le a
  have hpb := nativeProducerBudget_le h r
  have hi := (r.outer_word_load_bound a).1
  have hh := r.header_length_le
  have hN : r.table.count + 1 ≤ T := (r.native_lower_bounds a).2.2.trans (by dsimp [T]; omega)
  have ho : r.table.output.length ≤ 10 * T * H :=
    r.native_output_length_le.trans (Nat.mul_le_mul_right H (Nat.mul_le_mul_left 10 hN))
  have hhT := Nat.mul_le_mul_right H hT
  have hTH := Nat.mul_le_mul_left T hH2
  have h1 := Nat.mul_le_mul hT (show 1 ≤ H ^ 2 by nlinarith)
  change r.joinBudget h ≤ 10 ^ 8 * T * H ^ 2
  unfold NativeRequest.joinBudget FramedPair.cost
  change 2 * (2 * r.headerBudget + 2 * nativeProducerBudget h r +
    300 * (r.word.length + r.header.length + r.table.output.length + 1)) + 2 ≤ _
  change r.headerBudget ≤ 10 ^ 6 * T * H ^ 2 at hhb
  change nativeProducerBudget h r ≤ 10 ^ 5 * T * H at hpb
  change r.word.length ≤ 5000 * T * H at hi
  change r.header.length ≤ 10 * H at hh
  nlinarith

/-- `prop:time`, paper/paper.tex: the complete
actual native recovery, including full padded-packet cleanup and the
centered prefix decoder, has one native-clock factor and a fixed fourth
power of actual binary width. -/
theorem NativeRequest.recoveryBudget_le
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) :
    r.recoveryBudget h ≤ 10 ^ 16 * (TSK packetCallee + 10) *
      (StagePrint.fullTableCost (NativeTableFrame.publishedAlgorithm h) r.table + 1) *
        (r.packet.hint + 1) ^ 4 := by
  let a := NativeTableFrame.publishedAlgorithm h
  let T := StagePrint.fullTableCost a r.table + 1
  let H := r.packet.hint + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hH24 : H ^ 2 ≤ H ^ 4 := Nat.pow_le_pow_right hH (by decide)
  have hJ := r.joinBudget_le h
  change r.joinBudget h ≤ 10 ^ 8 * T * H ^ 2 at hJ
  have hN : r.table.count + 1 ≤ T := (r.native_lower_bounds a).2.2.trans (by dsimp [T]; omega)
  have hP := r.prefix.budget_le
  change r.prefix.budget ≤ 10 ^ 12 * (TSK packetCallee + 10) *
    (tableNaturals r.table).length.succ * H ^ 4 at hP
  rw [tableNaturals_length] at hP
  have hPT := Nat.mul_le_mul_left (10 ^ 12 * (TSK packetCallee + 10))
    (Nat.mul_le_mul_right (H ^ 4) hN)
  have hH4 : 1 ≤ H ^ 4 := Nat.one_le_pow _ _ hH
  have h1 := Nat.mul_le_mul hT hH4
  have h2 := Nat.mul_le_mul_left T hH24
  have h3 := Nat.mul_le_mul_right (T * H ^ 4) (show 10 ≤ TSK packetCallee + 10 by omega)
  change r.recoveryBudget h ≤ 10 ^ 16 * (TSK packetCallee + 10) * T * H ^ 4
  unfold NativeRequest.recoveryBudget
  nlinarith

end NearQuarticWires.StageRecovery
