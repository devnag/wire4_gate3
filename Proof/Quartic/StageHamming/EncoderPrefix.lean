import Proof.Quartic.StageHamming.ColumnBit

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition`, paper/paper.tex: the canonical
block encoder after its first `k` input data coordinates, read from
their actual packed scalar code and original block offset. -/
def encoderPrefix (P : StarParams) (code base q k : ℕ) : Bool :=
  PrimT.C4Geo.xr (fun m => code.testBit (base + m) &&
    PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P m) q) k

/-- `imp:partition`, paper/paper.tex: one additional
data bit contributes its actual canonical column by xor. -/
theorem encoderPrefix_succ (P : StarParams) (code base q k : ℕ) :
    encoderPrefix P code base q (k + 1) =
      xor (encoderPrefix P code base q k)
        (code.testBit (base + k) && PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P k) q) := rfl

/-- `imp:partition`, paper/paper.tex: the completed
scalar prefix is exactly the original canonical block encoder. -/
theorem encoderPrefix_eq_encB (P : StarParams) (code base q : ℕ) :
    encoderPrefix P code base q (PrimT.C4Geo.dB P) =
      PrimT.C4Geo.encB P (fun m => code.testBit (base + m)) q := rfl

end NearQuarticWires.StageHamming
