import Proof.Quartic.StageColumns.Columns

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

/-- `prop:time`, paper/paper.tex: direct bit output
has a fixed cubic source clock per actual canonical column. -/
theorem columnClock_le (P : StarParams) : columnClock P ≤ 120 * (P.n + 2) ^ 3 := by
  have hbit := bitClock_le P
  have hwidth := (dimensions_le P).1
  have hmain := Nat.mul_le_mul (show PrimT.C4Geo.width P ≤ P.n + 2 by omega)
    (show bitClock P + 9 ≤ 100 * (P.n + 2) ^ 2 + 9 by omega)
  unfold columnClock
  nlinarith only [hmain]

/-- `prop:time`, paper/paper.tex: both physical
column loops have one fixed quartic source clock in original arity. -/
theorem columnsClock_le (P : StarParams) : columnsClock P ≤ 140 * (P.n + 2) ^ 4 := by
  let V := P.n + 2
  have hv : 1 ≤ V := by dsimp [V]; omega
  have hv3 : 1 ≤ V ^ 3 := Nat.one_le_pow _ _ hv
  have hv4 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ hv
  have hcolumn := columnClock_le P
  have hfit : columnClock P + 4 ≤ 124 * V ^ 3 := by change columnClock P ≤ 120 * V ^ 3 at hcolumn; omega
  have hdim : PrimT.C4Geo.dRow P ≤ V := by have h := (dimensions_le P).2; dsimp [V]; omega
  unfold columnsClock
  calc
    _ ≤ V * (124 * V ^ 3) + 4 := Nat.add_le_add_right (Nat.mul_le_mul hdim hfit) 4
    _ = 124 * V ^ 4 + 4 := by ring
    _ ≤ 140 * V ^ 4 := by omega

end NearQuarticWires.StageColumns
