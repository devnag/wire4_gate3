import Proof.Quartic.StagePullback.PointRequest

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: the binary sampled-pattern index has
exactly the same low-first digits as the canonical star error. -/
theorem errorBit_call_eq (P : StarParams) (right : Bool)
    (code : Fin (2 ^ SeedFix.callKh P)) (x : Fin P.n) :
    errorBit P.b (P.r / 2) P.s right code.val x.val =
      P.errorVector (if right then P.rightBlock else P.leftBlock)
        ((SeedFix.callEqv P).symm code) x := by
  let c : Fin ((P.b + 1) ^ (P.r / 2)) :=
    ⟨code.val, by rw [SeedFix.callN_eq]; exact code.isLt⟩
  exact errorBit_eq P right c x

/-- `imp:pullback`, paper/paper.tex: the literal
coordinate flip is completely determined by compact scalar metadata. -/
def PointRequest.flip (q : PointRequest) (x : Fin q.parameters.n) : Bool :=
  flipBit q.parameters.r q.parameters.b q.parameters.s
    (translationNumber q.parameters q.translation) q.left.val q.right.val x.val
    q.useLeft q.useRight

/-- `imp:pullback` and Step 4 of `sec:algorithm`, paper/paper.tex: the actual requested original-coordinate
point is the canonical Hamming encoder bit xor its physically decoded
translation and selected error bits. -/
theorem PointRequest.point_scalar (q : PointRequest) (x : Fin q.parameters.n) :
    q.point x = xor (PrimT.C4Geo.ctrBit q.parameters q.row.val q.column.val x.val)
      (q.flip x) := by
  unfold PointRequest.point PointRequest.flip flipBit
  rw [PrimT.C4Geo.centerAt_bit, offsetBit_eq,
    errorBit_call_eq q.parameters false, errorBit_call_eq q.parameters true]
  simp only [Bool.false_eq_true, if_false, if_true, Bool.xor_assoc]

end NearQuarticWires.StagePullback
