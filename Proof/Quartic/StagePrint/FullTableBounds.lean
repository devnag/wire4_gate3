import Proof.Quartic.StagePrint.FullTable
import Proof.MachineModel.OrdinaryMatrixBatchAllRanksBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `lem:print`, paper/paper.tex: the actual affine-cut input has linear cut count and polynomial bit height. -/
theorem table_input_length (r : TableRequest) :
    (MatrixScoreBatch.physicalInput r.matrix).length ≤
      100 * (r.matrix.U + 1) * (r.matrix.d + r.matrix.p + 1) ^ 2 := by
  let H := r.matrix.d + r.matrix.p + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hH2 : H ≤ H ^ 2 := by simpa only [pow_two] using Nat.le_mul_self H
  have h1 : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ hH
  have hd : natBitLength r.matrix.d ≤ H := by
    have := Nat.log_le_self 2 r.matrix.d
    dsimp [natBitLength, H]
    omega
  have hp : natBitLength r.matrix.p ≤ H := by
    have := Nat.log_le_self 2 r.matrix.p
    dsimp [natBitLength, H]
    omega
  have hg : natBitLength r.matrix.Gates ≤ H :=
    (MatrixBatchAllRanksBounds.gate_width r.matrix).trans (by dsimp [H]; omega)
  have hw : natBitLength r.matrix.width ≤ H :=
    (MatrixScoreBatch.natBitLength_width_le_succ r.matrix).trans (by dsimp [H]; omega)
  have hwd : r.matrix.width ≤ 2 * H := r.matrix.widthLe.trans (by dsimp [H]; omega)
  have hd0 : r.matrix.d ≤ H := by dsimp [H]; omega
  have hp0 : r.matrix.p ≤ H := by dsimp [H]; omega
  have hcols := Nat.mul_le_mul hd0 (show 2 * r.matrix.width + 1 ≤ 5 * H by omega)
  have hcut := Nat.mul_le_mul (show 2 * r.matrix.width + 2 ≤ 6 * H by omega)
    (show 2 * r.matrix.p + 3 ≤ 5 * H by omega)
  have hcuts := Nat.mul_le_mul r.cuts_le hcut
  have hword := MatrixScoreBatch.word_length r.matrix
  have hphys : (MatrixScoreBatch.physicalInput r.matrix).length = 2 * (MatrixScoreBatch.word r.matrix).length + 1 :=
    frame_length _
  simp only [MatrixScoreBatch.header, List.length_append,
    MatrixScoreRawGateBounds.natWord_length, MatrixScorePhi.columnsWord_length,
    MatrixScoreBatch.cols_length] at hword
  change r.matrix.cuts.length * _ ≤ r.matrix.U * _ at hcuts
  change (MatrixScoreBatch.word r.matrix).length =
    2 * natBitLength r.matrix.d + 1 + (2 * natBitLength r.matrix.p + 1) +
      (2 * natBitLength r.matrix.Gates + 1) + (2 * natBitLength r.matrix.width + 1) +
      r.matrix.d * (2 * r.matrix.width + 1) +
      r.matrix.cuts.length * ((2 * r.matrix.width + 2) * (2 * r.matrix.p + 3)) at hword
  change (MatrixScoreBatch.physicalInput r.matrix).length ≤ 100 * (r.matrix.U + 1) * H ^ 2
  nlinarith

/-- `lem:print`, paper/paper.tex: loading every dimension field costs a fixed linear multiple of its actual length. -/
theorem table_load_cost (r : TableRequest) :
    r.loadCost ≤ 100 * ((MatrixScoreBatch.physicalInput r.matrix).length + r.count + r.q + 1) := by
  have hm : r.q - 1 ≤ r.q := Nat.sub_le _ _
  have hq : 3 ≤ r.q := by unfold TableRequest.q; omega
  simp only [TableRequest.loadCost, Top.loadCost, Top.loadRec, Top.loadChainCost, frame_length,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- `lem:print`, paper/paper.tex: every loading and signed decoding pass fits the quadratic table envelope. -/
theorem fullTableCost_bound (a : WilliamsAlgorithm) (r : TableRequest) :
    fullTableCost a r ≤ (CompetitorCountTable.coefficient a + 13000) *
      (r.matrix.U + 1) ^ 2 * (r.matrix.d + r.matrix.p + 1) ^ CompetitorCrossScheduler.exponent a := by
  let H := r.matrix.d + r.matrix.p + 1
  let V := (r.matrix.U + 1) ^ 2
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hH2 : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ hH
  have hsmall : H ≤ H ^ 2 := by simpa only [pow_two] using Nat.le_mul_self H
  have hV : 1 ≤ V := Nat.one_le_pow _ _ (by omega)
  have hN : r.count ≤ V := by dsimp [TableRequest.count, V]; nlinarith
  have hU : r.matrix.U + 1 ≤ V := by dsimp [V]; nlinarith
  have hQ : r.q ≤ 3 * H := by dsimp [TableRequest.q, H]; omega
  have htime := CompetitorCountTable.budget_bound a r.matrix r.q
    (by rw [CompetitorSameBucketColdDense.width_eq]; rfl)
  have hload := table_load_cost r
  have hi := table_input_length r
  have hi' : (MatrixScoreBatch.physicalInput r.matrix).length ≤ 100 * V * H ^ 2 := by
    exact hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 100 hU))
  have hNQ := Nat.mul_le_mul hN hQ
  have hNV := Nat.mul_le_mul hN hH2
  have hHV := Nat.mul_le_mul hV hsmall
  have hVH := Nat.mul_le_mul_left V hsmall
  have he : H ^ 2 ≤ H ^ CompetitorCrossScheduler.exponent a :=
    Nat.pow_le_pow_right hH (by unfold CompetitorCrossScheduler.exponent; omega)
  have hem := Nat.mul_le_mul_left V he
  have hm : r.q - 1 ≤ r.q := Nat.sub_le _ _
  change CompetitorCountTable.budget a r.matrix r.q + 1 ≤
    CompetitorCountTable.coefficient a * V * H ^ CompetitorCrossScheduler.exponent a at htime
  change fullTableCost a r ≤ (CompetitorCountTable.coefficient a + 13000) * V * H ^ CompetitorCrossScheduler.exponent a
  unfold fullTableCost signedTableCost NearCubicGates.Close.TabMachine.decodeCost
  change r.count ≤ V at hN
  dsimp only [TableRequest.count] at *
  nlinarith

end NearQuarticWires.StagePrint
