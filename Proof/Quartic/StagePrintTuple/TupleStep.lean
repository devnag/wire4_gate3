import Proof.Quartic.StagePrintTuple.RowContext
import Proof.Quartic.StagePrintTuple.TupleAlgebra
import Proof.Quartic.StagePrint.ChildTuples
import Proof.Gates.TabMachine.Occ3

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: a partial
Cartesian tuple has one full native row for every already processed
support variable, including the single zero-field empty tuple. -/
theorem tupleFields_row_length {ι : Type} (kids : ι→List (List ℤ)) (N : ℕ)
    (order : List ι) (hrow : ∀i∈order,∀row∈kids i,row.length=N) :
    ∀row∈tupleFields kids order,row.length=order.length*N := by
  induction order with
  | nil => simp [tupleFields_nil]
  | cons i order ih =>
    rw [tupleFields_cons]
    have htail := ih (fun j hj=>hrow j (by simp [hj]))
    have hstep := newT_mem_length N (order.length*N) (kids i) (tupleFields kids order)
      (hrow i (by simp)) htail
    simpa only [List.length_cons,Nat.succ_mul,Nat.add_comm] using hstep

/-- `lem:print`, paper/paper.tex: the actual
Cartesian machine receives the current original child pool and the
already processed suffix of the literal ascending support list. -/
def RowContext.tupleStepRequest (r : RowContext) (L : ℕ) (hL : 1≤L)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (order : List (Fin (17*(Builder.allGates r.header.call).length))) : StagePrint.ChildTupleRequest where
  L := L
  N := 2*NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.header.prepared.starParams+1
  M := order.length*(2*NearCubicWires.WireExponent3_5.PrimT.C4Geo.width r.header.prepared.starParams+1)
  children := r.nativeKids i
  tuples := tupleFields r.nativeKids order
  width_pos := hL
  children_length := r.nativeKids_row_length i
  tuples_length := tupleFields_row_length r.nativeKids _ order
    (fun j _=>r.nativeKids_row_length j)

/-- `lem:print`, paper/paper.tex: the genuine
Cartesian child-step output is the exact next partial tuple stream,
with each new original child preceding the complete old suffix. -/
theorem RowContext.tupleStepRequest_output (r : RowContext) (L : ℕ) (hL : 1≤L)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (order : List (Fin (17*(Builder.allGates r.header.call).length))) :
    (r.tupleStepRequest L hL i order).output=fieldsRecs L (tupleFields r.nativeKids (i::order)) := by
  change fieldsRecs L (newT (r.nativeKids i) (tupleFields r.nativeKids order))=_
  rw [tupleFields_cons]

/-- `lem:print`, paper/paper.tex: the actual
Cartesian request's old and new counts are the genuine finite pool
and suffix tuple counts; the next count is their exact product. -/
theorem RowContext.tupleStepRequest_count (r : RowContext) (L : ℕ) (hL : 1≤L)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (order : List (Fin (17*(Builder.allGates r.header.call).length))) :
    (tupleFields r.nativeKids (i::order)).length=
      (r.tupleStepRequest L hL i order).children.length*
        (r.tupleStepRequest L hL i order).tuples.length := by
  rw [tupleFields_cons,newT_length]
  rfl

end NearQuarticWires.StageTuple
