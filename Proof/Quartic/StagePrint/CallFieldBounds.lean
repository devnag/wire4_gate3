import Proof.Quartic.StagePrint.RawCallGate

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: actual normalized original fields have a dimension-polynomial binary width. -/
theorem call_original_field_width {n : ℕ} (g : NormalizedThresholdGate n) (hB : GateBits (Call.B0 n) g) :
    (originalChildRequest (Call.B0 n) g hB).W+1≤4*(n+1)^2+5 := by
  have hc : Nat.clog 2 (n+1)≤n+1 := by
    apply Nat.clog_le_of_le_pow
    exact Nat.lt_two_pow_self.le
  change (4*n*Nat.clog 2 (n+1)+Nat.clog 2 (n+1)+4)+1≤_
  have hh:=Nat.mul_le_mul_left (4*n+1) hc
  nlinarith

end NearQuarticWires.StagePrint
