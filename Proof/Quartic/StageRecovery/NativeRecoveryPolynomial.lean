import Proof.Quartic.StageRecovery.NativeRecoveryBudget
import Proof.Quartic.StageRecovery.NativeWidth

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the published
native recovery coefficient includes the actual source algorithm,
complete centered packet decoder and constant-factor frame handling. -/
noncomputable def nativeRecoveryPolynomialCoefficient
    (h : Bindings.Williams14.Williams14_Corollary4_4) : ℕ :=
  10 ^ 16 * (TSK packetCallee + 10) *
    (CompetitorCountTable.coefficient (NativeTableFrame.publishedAlgorithm h) + 13001) * 16 ^ 4

/-- `prop:time`, paper/paper.tex: physical recovery
adds only a fixed fourth power to the published algorithm's polynomial
bit-width exponent. -/
noncomputable def nativeRecoveryPolynomialExponent
    (h : Bindings.Williams14.Williams14_Corollary4_4) : ℕ :=
  CompetitorCrossScheduler.exponent (NativeTableFrame.publishedAlgorithm h) + 4

/-- `prop:time`, paper/paper.tex: the native
census and two width powers regroup without changing any exponent. -/
theorem nativeCost_reassociate (C A N R B e : ℕ) :
    C * (A * N * B ^ e) * (R * B) ^ 4 =
      (C * A * R ^ 4) * N * B ^ (e + 4) := by
  rw [mul_pow, pow_add]
  ring

/-- `prop:time`, paper/paper.tex: the complete
actual cold native recovery preserves the quadratic half-table census
and has fixed polynomial dependence only on native dimension, actual
physical coefficient width and the residue modulus's binary length. -/
theorem NativeRequest.recoveryBudget_polynomial
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : NativeRequest) :
    r.recoveryBudget h ≤ nativeRecoveryPolynomialCoefficient h * (r.table.matrix.U + 1) ^ 2 *
      (r.table.matrix.d + r.table.matrix.p + natBitLength r.modulus + 1) ^
        nativeRecoveryPolynomialExponent h := by
  let a := NativeTableFrame.publishedAlgorithm h
  let N := (r.table.matrix.U + 1) ^ 2
  let B := r.table.matrix.d + r.table.matrix.p + natBitLength r.modulus + 1
  let e := CompetitorCrossScheduler.exponent a
  let A := CompetitorCountTable.coefficient a + 13001
  let C := 10 ^ 16 * (TSK packetCallee + 10)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hN : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hpow : 1 ≤ B ^ e := Nat.one_le_pow _ _ hB
  have hp := StagePrint.fullTableCost_bound a r.table
  have hb : (r.table.matrix.d + r.table.matrix.p + 1) ^ e ≤ B ^ e :=
    Nat.pow_le_pow_left (by dsimp [B]; omega) _
  have ht : StagePrint.fullTableCost a r.table ≤
      (CompetitorCountTable.coefficient a + 13000) * N * B ^ e :=
    hp.trans (Nat.mul_le_mul_left _ hb)
  have ht1 : StagePrint.fullTableCost a r.table + 1 ≤ A * N * B ^ e := by
    have hnp := Nat.mul_le_mul hN hpow
    dsimp [A]
    nlinarith
  have hw := r.native_hint_linear
  change r.packet.hint + 1 ≤ 16 * B at hw
  calc
    r.recoveryBudget h ≤ C * (StagePrint.fullTableCost a r.table + 1) * (r.packet.hint + 1) ^ 4 :=
      r.recoveryBudget_le h
    _ ≤ C * (A * N * B ^ e) * (16 * B) ^ 4 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left C ht1) (Nat.pow_le_pow_left hw 4)
    _ = nativeRecoveryPolynomialCoefficient h * (r.table.matrix.U + 1) ^ 2 *
        B ^ nativeRecoveryPolynomialExponent h :=
      nativeCost_reassociate C A N 16 B e

end NearQuarticWires.StageRecovery
