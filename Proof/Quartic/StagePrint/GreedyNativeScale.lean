import Proof.Quartic.StageGreedyNativeData.Final
import Proof.Quartic.StageNativeWidth.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.GreedyCost
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5

/-- `imp:partition` and `prop:time`, paper/paper.tex: the complete padded native square has at
most twice the original column count, even when the free dimension
is odd. Its quadratic half-table scale has at most eight times that count. -/
theorem native_scale_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ((StageGreedyNativeData.nativeRequest r).table.matrix.U+1)^2≤8*r.child.cellCall.ncol := by
  let U:=2^PrimT.C4Geo.dRow (GreedyCollector.star r)
  let R:=2^PrimT.C4Geo.dR (GreedyCollector.star r)
  have hcount : U*R=r.child.cellCall.ncol:=StageGreedyNativeData.original_count r
  have hbalance : PrimT.C4Geo.dRow (GreedyCollector.star r)≤
      PrimT.C4Geo.dR (GreedyCollector.star r)+1 :=
    (GreedyCollector.star r).centerBits_balanced.2
  have hUR : U≤2*R := by
    have h:=Nat.pow_le_pow_right (by decide : 0<2) hbalance
    simpa only [pow_succ,Nat.mul_comm] using h
  have hU : 1≤U:=Nat.one_le_two_pow
  have hmul:=Nat.mul_le_mul_left U hUR
  change (U+1)^2≤8*r.child.cellCall.ncol
  nlinarith

/-- `imp:partition` and `prop:time`, paper/paper.tex: the actual native row dimension is bounded
by the original arity, without a table or geometric premise. -/
theorem native_dimension_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (StageGreedyNativeData.nativeRequest r).table.matrix.d≤r.child.call.n := by
  let entry:=GreedyEntry.Request.mk r ⟨0,StageLiftSourceCost.walkCount_pos r⟩
  exact (StageNativeWidth.nativeDimensions_le entry.rowContext).2

/-- `prop:time`, paper/paper.tex: the actual
combined source-algorithm bit parameter is polynomial in original
arity, independently of raw target integer heights. -/
theorem native_bit_parameter_polynomial (B1 B2 : ℕ) :
    ∃ C E : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      (StageGreedyNativeData.nativeRequest r).table.matrix.d+
        (StageGreedyNativeData.nativeRequest r).table.matrix.p+
        natBitLength (StageGreedyNativeData.nativeRequest r).modulus+1≤C*(r.child.call.n+1)^E := by
  obtain ⟨C,E,h⟩:=StageGreedyNativeData.native_widths_bound B1 B2
  refine ⟨C+1,E+1,?_⟩
  intro r
  have hn := native_dimension_le r
  have hb := h r
  have hmono : (r.child.call.n+1)^E≤(r.child.call.n+1)^(E+1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsource : r.child.call.n+1≤(r.child.call.n+1)^(E+1) :=
    Nat.le_self_pow (by omega) _
  have hs:=Nat.mul_le_mul_left C hmono
  calc
    _ ≤ C*(r.child.call.n+1)^E+(r.child.call.n+1) := by omega
    _ ≤ C*(r.child.call.n+1)^(E+1)+(r.child.call.n+1)^(E+1) := by omega
    _ = _ := by ring

end NearQuarticWires.StagePrint.GreedyCost
