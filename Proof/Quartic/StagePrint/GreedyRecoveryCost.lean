import Proof.Quartic.StagePrint.GreedyNativeScale
import Proof.Quartic.StageRecovery.NativeRecoveryPolynomial

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.GreedyCost
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5

/-- `prop:time`, paper/paper.tex: the actual
published native algorithm and centered-prefix recovery cost only the
original column count times a fixed polynomial in original arity. -/
theorem native_recovery_selected
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    ∃ K e : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      (StageGreedyNativeData.nativeRequest r).recoveryBudget h ≤
        K*r.child.cellCall.ncol*(r.child.call.n+1)^e := by
  obtain ⟨C,E,hbit⟩:=native_bit_parameter_polynomial B1 B2
  let a:=StageRecovery.nativeRecoveryPolynomialCoefficient h
  let b:=StageRecovery.nativeRecoveryPolynomialExponent h
  refine ⟨a*8*C^b,E*b,?_⟩
  intro r
  have hp:=(StageGreedyNativeData.nativeRequest r).recoveryBudget_polynomial h
  have hs:=native_scale_le r
  have hb:=Nat.pow_le_pow_left (hbit r) b
  calc
    _ ≤ a*((StageGreedyNativeData.nativeRequest r).table.matrix.U+1)^2*
        ((StageGreedyNativeData.nativeRequest r).table.matrix.d+
          (StageGreedyNativeData.nativeRequest r).table.matrix.p+
          natBitLength (StageGreedyNativeData.nativeRequest r).modulus+1)^b := hp
    _ ≤ a*(8*r.child.cellCall.ncol)*(C*(r.child.call.n+1)^E)^b :=
      Nat.mul_le_mul (Nat.mul_le_mul_left a hs) hb
    _ = _ := by rw [mul_pow,←pow_mul]; ring

end NearQuarticWires.StagePrint.GreedyCost
