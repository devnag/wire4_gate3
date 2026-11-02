import Proof.Quartic.StagePullback.Canonical

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: a compact canonical center and its
two sampled star errors, with independently selected corners. -/
structure PointRequest where
  parameters : StarParams
  translation : parameters.Translation
  row : Fin (2 ^ PrimT.C4Geo.dRow parameters)
  column : Fin (2 ^ PrimT.C4Geo.dR parameters)
  left : Fin (2 ^ SeedFix.callKh parameters)
  right : Fin (2 ^ SeedFix.callKh parameters)
  useLeft : Bool
  useRight : Bool

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: all point-construction data are explicit scalar
codes; no center table or decoded point is part of the input. -/
def PointRequest.word (r : PointRequest) : List Bool :=
  natWord r.parameters.n ++ natWord r.parameters.r ++ natWord r.parameters.b ++
    natWord r.parameters.s ++ natWord (translationNumber r.parameters r.translation) ++
    natWord r.row.val ++ natWord r.column.val ++ natWord r.left.val ++ natWord r.right.val ++
    [r.useLeft, r.useRight]

/-- `imp:pullback` and Step 4 of `sec:algorithm`, paper/paper.tex: the literal requested point in original
coordinate order, using the same center generator as table printing. -/
def PointRequest.point (r : PointRequest) : BitInput r.parameters.n :=
  fun x => xor (xor (PrimT.C4Geo.centerAt r.parameters r.translation r.row.val r.column.val x)
    (r.useLeft && r.parameters.errorVector r.parameters.leftBlock
      ((SeedFix.callEqv r.parameters).symm r.left) x))
    (r.useRight && r.parameters.errorVector r.parameters.rightBlock
      ((SeedFix.callEqv r.parameters).symm r.right) x)

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the point is packed low-first for the actual predicate evaluator. -/
def PointRequest.packed (r : PointRequest) : ℕ :=
  CanonicalBinary.bitsValue (List.ofFn r.point)

def PointRequest.output (r : PointRequest) : List Bool := frame (natWord r.packed)

/-- `imp:pullback`, paper/paper.tex: the unshifted
request is exactly the canonical shared-generator center. -/
theorem PointRequest.point_center (r : PointRequest) (hl : r.useLeft = false)
    (hr : r.useRight = false) :
    r.point = PrimT.C4Geo.centerAt r.parameters r.translation r.row.val r.column.val := by
  ext x
  simp [PointRequest.point, hl, hr]

/-- `imp:pullback`, paper/paper.tex: selecting both
errors gives the literal original-coordinate fourth corner. -/
theorem PointRequest.point_both (r : PointRequest) (hl : r.useLeft = true)
    (hr : r.useRight = true) :
    r.point = xorInput
      (xorInput (PrimT.C4Geo.centerAt r.parameters r.translation r.row.val r.column.val)
        (r.parameters.errorVector r.parameters.leftBlock ((SeedFix.callEqv r.parameters).symm r.left)))
      (r.parameters.errorVector r.parameters.rightBlock ((SeedFix.callEqv r.parameters).symm r.right)) := by
  ext x
  simp [PointRequest.point, xorInput, hl, hr]

end NearQuarticWires.StagePullback
