import Proof.Quartic.StageCert.StructuralBuilder

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch

/-- `prop:time`, paper/paper.tex: the exact source mask
scan has polynomial arithmetic cost in the original dimension and retained
source length, including both side scans and initialization. -/
theorem structural_steps_le (n r L : ℕ) (hr : r≤n) :
    2*(r/2)*(1204*(L+2)^3+2)+40≤1246*(n+1)*(L+2)^3 := by
  have hh : 2*(r/2)≤n := by omega
  have hmul := Nat.mul_le_mul_right (1204*(L+2)^3+2) hh
  have hp : 1≤(L+2)^3 := Nat.pow_pos (by omega)
  nlinarith

/-- `prop:time`, paper/paper.tex: compiling the original
source mask adds only the explicit quadratic binary-register overhead. -/
theorem structural_bit_cost_le (n r L W : ℕ) (hr : r≤n) :
    (2*(r/2)*(1204*(L+2)^3+2)+40)*KC W≤
      623000*(n+1)*(L+2)^3*(W+1)^2 := by
  have h := Nat.mul_le_mul_right (KC W) (structural_steps_le n r L hr)
  unfold KC at h ⊢
  convert h using 1
  ring

end NearQuarticWires.StageCert
