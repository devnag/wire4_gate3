import Proof.Quartic.StagePrint.CallFieldBounds
import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the public binary-size subroutine computes exactly the ceiling logarithm required by the original field width. -/
theorem clog_two_succ_eq_size (n : ℕ) : Nat.clog 2 (n+1)=Nat.size n := by
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    have:=Nat.lt_size_self n
    omega
  · apply Nat.size_le.mpr
    have:=Nat.le_pow_clog (by decide : 1<(2 : ℕ)) (n+1)
    omega

/-- `lem:print`, paper/paper.tex: the original normalized-call field width is computed from the actual input dimension by binary arithmetic. -/
theorem original_Lin_size {n : ℕ} (g : NormalizedThresholdGate n)
    (hB : NearCubicGates.Close.Tabulator.GateBits (Call.B0 n) g) :
    (originalChildRequest (Call.B0 n) g hB).W+1=(4*n+1)*Nat.size n+5 := by
  change 4*n*Nat.clog 2 (n+1)+Nat.clog 2 (n+1)+4+1=_
  rw [clog_two_succ_eq_size]
  ring

/-- `imp:pullback`, paper/paper.tex: the original child width and the affine target width remain dimension-polynomial. -/
theorem header_widths_le (n : ℕ) :
    (4*n+1)*Nat.size n+5≤4*(n+1)^2+5 ∧
      (4*n+1)*Nat.size n+5+n+6≤4*(n+1)^2+n+11 := by
  have hs : Nat.size n≤n+1 := by
    rw [←clog_two_succ_eq_size]
    apply Nat.clog_le_of_le_pow
    exact Nat.lt_two_pow_self.le
  have hh:=Nat.mul_le_mul_left (4*n+1) hs
  constructor <;> nlinarith

end NearQuarticWires.StagePrint.Header
