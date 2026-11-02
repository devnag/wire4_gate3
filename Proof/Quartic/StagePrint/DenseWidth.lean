import Proof.Quartic.StagePrint.NativeGeometry

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition` and `lem:print`, paper/paper.tex: the dense half-width depends only on the original
arity, so its physical formatter needs no decoded block geometry. -/
theorem native_width_eq_half (P : StarParams) :
    PrimT.C4Geo.width P = (P.n+1)/2 := by
  have hr := P.r_half_add
  have hb := P.r_mul_b_le
  have hmul : P.r*P.b = 2*(P.r/2*P.b) := by nlinarith
  have hsum := Nat.sub_add_cancel hb
  unfold PrimT.C4Geo.width PrimT.C4Geo.hL
  omega

end NearQuarticWires.StagePrint
