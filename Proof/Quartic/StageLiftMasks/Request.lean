import Proof.Quartic.StageLift.MasksContract

/-!
# The original edge requests of a printed walk

`def:mask` and `lem:print`, paper/paper.tex: the low-first walk ordinal determines the same
eight original structural queries in the residue and moment sources.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

theorem request_N (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N=r.child.selected.1.N :=
  (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).seed_N

noncomputable def maskMomentRequest (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) : MomentRequest B1 B2 where
  call := r.child.call
  selected := r.child.selected
  dispatched := r.child.dispatched
  witness := r.child.witness
  test := .finalError 0 0
  index := ⟨index.val,by
    change index.val<r.child.selected.1.N^8
    rw [←request_N]
    exact index.isLt⟩

theorem maskMomentRequest_walk (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) :
    (maskMomentRequest r index).walk=printWalkAt _ index := by
  funext l
  apply Fin.ext
  change index.val/r.child.selected.1.N^l.val%r.child.selected.1.N=_
  rw [printWalkAt_coordinate]
  exact congrArg (fun n=>index.val/n^l.val%n) (request_N r).symm

theorem maskMomentRequest_edge (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    (maskMomentRequest r index).edgeRequest edge=printMaskStructuralRequest r index edge := by
  unfold MomentRequest.edgeRequest printMaskStructuralRequest
  rw [maskMomentRequest_walk]
  rfl

theorem maskMomentRequest_structural (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    StagePrint.callStructural (maskMomentRequest r index).call
      (maskMomentRequest r index).rules (maskMomentRequest r index).walk edge=
    StagePrint.callStructural r.child.call
      (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) (printWalkAt _ index) edge := by
  rw [maskMomentRequest_walk]
  rfl

theorem maskMomentRequest_left (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    ((maskMomentRequest r index).edgeRequest edge).left.val=
      (printMaskStructuralRequest r index edge).left.val :=
  congrArg (fun q : StageMainMask.StructuralRequest B1 B2=>q.left.val)
    (maskMomentRequest_edge r index edge)

theorem maskMomentRequest_right (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    ((maskMomentRequest r index).edgeRequest edge).right.val=
      (printMaskStructuralRequest r index edge).right.val :=
  congrArg (fun q : StageMainMask.StructuralRequest B1 B2=>q.right.val)
    (maskMomentRequest_edge r index edge)

end NearQuarticWires.StageLiftMasks
