import Proof.Quartic.StageMainMask.StructuralFinal

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

/-- `def:mask` and `prop:time`, paper/paper.tex: the shared structural machine's exact ordinary reply
consists of the marker, actual Boolean value and final delimiter. -/
theorem structuralOutput_bytes {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    structuralOutput r = [true, structuralBit r, false] := rfl

end NearQuarticWires.StageMainMask
