import Proof.Quartic.StageHamming.DataPosition

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition`, paper/paper.tex: a Hamming
basis-column bit after the first `k` parity coordinates have been read. -/
def columnPrefix (i q k : ℕ) : Bool :=
  (q == i) || (List.range k).any fun t => (i + 1).testBit t && q + 1 == 2 ^ t

/-- `imp:partition`, paper/paper.tex: one more
parity position contributes precisely its specified binary check bit. -/
theorem columnPrefix_succ (i q k : ℕ) :
    columnPrefix i q (k + 1) =
      (columnPrefix i q k || ((i + 1).testBit k && q + 1 == 2 ^ k)) := by
  simp only [columnPrefix, List.range_succ, List.any_append, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_assoc]

/-- `imp:partition`, paper/paper.tex: a completed
parity scan is the literal column bit of the original Hamming basis. -/
theorem columnPrefix_eq_cwBit (P : StarParams) (i q : ℕ) :
    columnPrefix i q P.s = PrimT.C4Geo.cwBit P i q := rfl

end NearQuarticWires.StageHamming
