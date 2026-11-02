import Proof.Quartic.StageRecovery.NativeCost

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the actual
square native census has exactly twice the half-dimension plus one
binary bits, including the zero-dimensional case. -/
theorem native_count_bits (r : StagePrint.TableRequest) :
    natBitLength r.count = 2 * r.matrix.d + 1 := by
  unfold StagePrint.TableRequest.count MatrixScoreBatch.Request.U
  rw [← Nat.pow_add]
  simp [natBitLength, Nat.log_pow]
  omega

/-- `prop:time`, paper/paper.tex: the complete
actual decoder hint depends polynomially on native dimension, physical
coefficient width and modulus bits, not native output magnitude. -/
theorem NativeRequest.native_hint_linear (r : NativeRequest) :
    r.packet.hint + 1 ≤ 16 * (r.table.matrix.d + r.table.matrix.p + natBitLength r.modulus + 1) := by
  rw [← r.nativeHint_eq]
  unfold NativeRequest.nativeHint StagePrint.TableRequest.q
  rw [native_count_bits]
  omega

end NearQuarticWires.StageRecovery
