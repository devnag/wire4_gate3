import Proof.Quartic.StagePrint.GreedyRecoveryCost
import Proof.Quartic.StagePrint.NativeMiddleTarget
import Proof.Quartic.StageNativeHeader.Final

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.GreedyCost
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine

/-- `prop:time`, paper/paper.tex: the actual
recovery clock pays every byte of its literal retained input record. -/
theorem native_input_paid
    (h : Bindings.Williams14.Williams14_Corollary4_4) (r : StageRecovery.NativeRequest) :
    r.word.length ≤ r.recoveryBudget h := by
  unfold StageRecovery.NativeRequest.recoveryBudget StageRecovery.NativeRequest.joinBudget
    StageRecovery.FramedPair.cost
  omega

/-- `lem:print`, paper/paper.tex: the original
cut bytes and padded count are present in the actual nested native
input and are bounded by its literal finite length. -/
theorem header_stream_count_paid (r : Downstream.NativeHeaderRequest)
    (modulus targetCount : ℕ) :
    r.stream.length+r.table.count+1 ≤
      (NativeMiddle.word modulus r.table.word targetCount).length := by
  simp only [Downstream.NativeHeaderRequest.stream,NativeMiddle.word,
    TableRequest.word,Top.loadRec,MatrixScoreBatch.physicalInput,MatrixScoreBatch.word,
    frame_length,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega

/-- `prop:time`, paper/paper.tex: the actual
retained native input has the same selected original-column cost
bound as the complete physical recovery that consumes it. -/
theorem native_input_selected
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    ∃ K e : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      (StageGreedyNativeData.nativeRequest r).word.length ≤
        K*r.child.cellCall.ncol*(r.child.call.n+1)^e := by
  obtain ⟨K,e,hK⟩:=native_recovery_selected h B1 B2
  exact ⟨K,e,fun r=>(native_input_paid h _).trans (hK r)⟩

/-- `prop:time`, paper/paper.tex: the concrete
native-header printer has a selected original-column cost, including
its real canonical-column and complete cut-stream construction. -/
theorem native_header_selected
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    ∃ K e : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      let d:=(StageGreedyNativeData.nativeSupplier B1 B2).val r
      10^30*(d.headerRequest.parameters.n+d.native.table.matrix.p+2)^20*
        (d.headerRequest.stream.length+d.native.table.count+1) ≤
          K*r.child.cellCall.ncol*(r.child.call.n+1)^e := by
  obtain ⟨C,E,hC⟩:=native_bit_parameter_polynomial B1 B2
  obtain ⟨K,e,hK⟩:=native_input_selected h B1 B2
  refine ⟨10^30*(C+2)^20*K,(E+1)*20+e,?_⟩
  intro r
  let d:=(StageGreedyNativeData.nativeSupplier B1 B2).val r
  have hsize:=header_stream_count_paid d.headerRequest d.native.modulus d.native.targetCount
  change d.headerRequest.stream.length+d.native.table.count+1 ≤ d.native.word.length at hsize
  have hlength : d.native.word.length ≤ K*r.child.cellCall.ncol*(r.child.call.n+1)^e := hK r
  have hbase : r.child.call.n+1 ≤ (r.child.call.n+1)^(E+1) := Nat.le_self_pow (by omega) _
  have hmono : (r.child.call.n+1)^E ≤ (r.child.call.n+1)^(E+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp := hC r
  have hwidth : d.headerRequest.parameters.n+d.native.table.matrix.p+2 ≤
      (C+2)*(r.child.call.n+1)^(E+1) := by
    change r.child.call.n+(StageGreedyNativeData.nativeRequest r).table.matrix.p+2 ≤ _
    have hm:=Nat.mul_le_mul_left C hmono
    nlinarith only [hp,hm,hbase]
  change 10^30*(d.headerRequest.parameters.n+d.native.table.matrix.p+2)^20*
    (d.headerRequest.stream.length+d.native.table.count+1) ≤ _
  calc
    _ ≤ 10^30*((C+2)*(r.child.call.n+1)^(E+1))^20*
        (K*r.child.cellCall.ncol*(r.child.call.n+1)^e) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth 20))
        (hsize.trans hlength)
    _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring

end NearQuarticWires.StagePrint.GreedyCost
