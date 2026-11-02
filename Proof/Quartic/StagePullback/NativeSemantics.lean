import Proof.Quartic.StagePullback.NativeRow

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.Shared

def leftError (q : PointRequest) : BitInput q.parameters.n :=
  q.parameters.errorVector q.parameters.leftBlock ((SeedFix.callEqv q.parameters).symm q.left)

def rightError (q : PointRequest) : BitInput q.parameters.n :=
  q.parameters.errorVector q.parameters.rightBlock ((SeedFix.callEqv q.parameters).symm q.right)

def cornerIndex (q : PointRequest) : Fin 4 :=
  if q.useLeft then (if q.useRight then 0 else 1) else (if q.useRight then 2 else 3)

/-- `imp:pullback`, paper/paper.tex: the actual affine
flip is precisely the canonical offset and the two selected original
star-error vectors. -/
theorem flip_actual (q : PointRequest) : q.flip = fun x =>
    xor (xor (PrimT.C4Geo.offset q.parameters q.translation x) (q.useLeft && leftError q x))
      (q.useRight && rightError q x) := by
  funext x
  unfold PointRequest.flip flipBit
  rw [offsetBit_eq, errorBit_call_eq q.parameters false, errorBit_call_eq q.parameters true]
  rfl

/-- `imp:pullback`, paper/paper.tex: the scalar flags
select the literal corresponding corner of the actual canonical offset. -/
theorem flip_corner (q : PointRequest) : q.flip =
    PrimT.C4Geo.cornerPt (PrimT.C4Geo.offset q.parameters q.translation)
      (leftError q) (rightError q) (cornerIndex q) := by
  rw [flip_actual]
  funext x
  cases hl : q.useLeft <;> cases hr : q.useRight <;>
    simp [cornerIndex, PrimT.C4Geo.cornerPt, xorInput, hl, hr]

/-- `imp:pullback`, paper/paper.tex: the actual
original-coordinate point at arbitrary row and column center codes. -/
def affinePoint (q : PointRequest) (row column : ℕ) : BitInput q.parameters.n :=
  fun x => xor (xor (PrimT.C4Geo.centerAt q.parameters q.translation row column x)
    (q.useLeft && leftError q x)) (q.useRight && rightError q x)

/-- `imp:pullback`, paper/paper.tex: the selected
original-coordinate point is the same literal corner as the affine flip. -/
theorem affinePoint_corner (q : PointRequest) (row column : ℕ) :
    affinePoint q row column = PrimT.C4Geo.cornerPt
      (PrimT.C4Geo.centerAt q.parameters q.translation row column)
      (leftError q) (rightError q) (cornerIndex q) := by
  funext x
  cases hl : q.useLeft <;> cases hr : q.useRight <;>
    simp [affinePoint, cornerIndex, PrimT.C4Geo.cornerPt, xorInput, hl, hr]

/-- `imp:pullback`, paper/paper.tex: the retained
point request uses this same original-coordinate point at its actual
finite row and column codes. -/
theorem point_affinePoint (q : PointRequest) : q.point = affinePoint q q.row.val q.column.val := rfl

/-- `imp:pullback`, paper/paper.tex: original native
side order is exactly the canonical Hamming half-coordinate order. -/
theorem sideList_false (q : PointRequest) : sideList q false = PrimT.C4Geo.side q.parameters := by
  simp [sideList, PrimT.C4Geo.side]

/-- `imp:pullback`, paper/paper.tex: the actual affine
coordinate pullback is evaluated on the SAME canonical Hamming generator
on both halves, with no supplied decoded center. -/
theorem pullPoint_canonical (q : PointRequest) (row column : ℕ) :
    Pool.pullPoint (sideList q false) (flipList q)
      (MatrixScorePhi.value (PrimT.C4Geo.cols q.parameters) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols q.parameters) column) = affinePoint q row column := by
  rw [sideList_false, flipList, flip_corner]
  exact (PrimT.C4Geo.pull_flip q.parameters q.translation row column
    (leftError q) (rightError q) (cornerIndex q)).trans (affinePoint_corner q row column).symm

/-- `imp:pullback`, paper/paper.tex: exchanging the
physical side of every original coordinate exchanges its two native
assignment words and their actual rank counters. -/
theorem pointList_swap (aL aR : ℕ) : ∀ (cs : List (Bool × Bool)) (kL kR : ℕ),
    Pool.pointList aL aR (cs.map fun p => (!p.1, p.2)) kL kR =
      Pool.pointList aR aL cs kR kL
  | [], _, _ => rfl
  | (side, flip) :: cs, kL, kR => by
    cases side <;> simp [Pool.pointList, pointList_swap]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the certificate's physical side exchange is exactly native
row/column transposition for the original coordinate pullback. -/
theorem pullPoint_swap (q : PointRequest) (aL aR : ℕ) :
    Pool.pullPoint (n := q.parameters.n) (sideList q true) (flipList q) aL aR =
      Pool.pullPoint (n := q.parameters.n) (sideList q false) (flipList q) aR aL := by
  have hp : (List.ofFn fun j : Fin q.parameters.n =>
      ((sideList q true).getD j false, (flipList q).getD j false)) =
      (List.ofFn fun j : Fin q.parameters.n =>
        ((sideList q false).getD j false, (flipList q).getD j false)).map (fun p => (!p.1, p.2)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    simp only [Function.comp_def, sideList, flipList, PrimT.C4Geo.ofFn_getD]
    simp
  funext x
  unfold Pool.pullPoint
  rw [hp, pointList_swap]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the exact native signed affine child has precisely the
original child's value at the actual canonical star corner under the
SAME Hamming map, with the certificate's requested transpose. -/
theorem nativeChild_eval (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) (row column : ℕ) :
    (nativeChild q e transpose).eval (Pool.centerInput (PrimT.C4Geo.width q.parameters)
      (MatrixScorePhi.value (PrimT.C4Geo.cols q.parameters) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols q.parameters) column)) =
      e.eval (affinePoint q (if transpose then column else row) (if transpose then row else column)) := by
  have hl := routes_length_le q e transpose
  unfold nativeChild
  rw [Pool.pullDense_eval (sideList q transpose) (flipList q) (PrimT.C4Geo.width q.parameters)
    (MatrixScorePhi.value (PrimT.C4Geo.cols q.parameters) row)
    (MatrixScorePhi.value (PrimT.C4Geo.cols q.parameters) column) e hl.1 hl.2]
  cases transpose with
  | false =>
    simpa only [Bool.false_eq_true, if_false] using congrArg e.eval (pullPoint_canonical q row column)
  | true =>
    rw [pullPoint_swap]
    simpa only [if_true] using congrArg e.eval (pullPoint_canonical q column row)

end NearQuarticWires.StagePullback.NativeRows
