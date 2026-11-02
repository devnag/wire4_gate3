import Proof.Quartic.StagePrintTuple.TupleStep
import Proof.Quartic.StagePrintTuple.RecordOutputs

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: after a
computed number of reverse iterations, the processed variables are
exactly the final suffix of the literal ascending support list. -/
def processedSupport {ι : Type} (order : List ι) (done : ℕ) : List ι :=
  order.drop (order.length-done)

/-- `lem:print`, paper/paper.tex: the processed
suffix has exactly the physically maintained processed support count. -/
theorem processedSupport_length {ι : Type} (order : List ι) (done : ℕ)
    (hd : done≤order.length) : (processedSupport order done).length=done := by
  simp only [processedSupport,List.length_drop]
  omega

/-- `lem:print`, paper/paper.tex: decrementing
the real reverse index selects precisely the next original variable
that is prepended to the already processed support suffix. -/
theorem processedSupport_succ {ι : Type} (order : List ι) (done : ℕ)
    (hd : done<order.length) :
    processedSupport order (done+1)=
      order[order.length-(done+1)]::processedSupport order done := by
  unfold processedSupport
  have hi : order.length-(done+1)<order.length := by omega
  rw [List.drop_eq_getElem_cons hi]
  congr 1
  congr 1
  omega

/-- `lem:print`, paper/paper.tex: every current
suffix tuple segment stores its actual signed fields followed by one
real list delimiter, including a singleton empty initial tuple. -/
def tupleSegment {ι : Type} (L : ℕ) (kids : ι→List (List ℤ))
    (order : List ι) (done : ℕ) : List Bool :=
  fieldsRecs L (tupleFields kids (processedSupport order done))++[false]

/-- `lem:print`, paper/paper.tex: earlier tuple
segments are retained without recopying, while the current segment is
addressed by its actual physical source cursor. -/
def tupleHistoryPrefix {ι : Type} (L : ℕ) (kids : ι→List (List ℤ))
    (order : List ι) (done : ℕ) : List Bool :=
  (List.range done).flatMap (tupleSegment L kids order)

/-- `lem:print`, paper/paper.tex: the complete
finite history contains the original empty-tuple segment and every
subsequent exact suffix tuple segment once. -/
def tupleHistory {ι : Type} (L : ℕ) (kids : ι→List (List ℤ))
    (order : List ι) (done : ℕ) : List Bool :=
  tupleHistoryPrefix L kids order (done+1)

/-- `lem:print`, paper/paper.tex: the current
history cursor follows exactly the already retained earlier segments. -/
theorem tupleHistory_eq {ι : Type} (L : ℕ) (kids : ι→List (List ℤ))
    (order : List ι) (done : ℕ) :
    tupleHistory L kids order done=
      tupleHistoryPrefix L kids order done++tupleSegment L kids order done := by
  simp only [tupleHistory,tupleHistoryPrefix,List.range_succ,List.flatMap_append,
    List.flatMap_singleton]

/-- `lem:print`, paper/paper.tex: a new actual
Cartesian output is appended after the whole previous history exactly
once, and becomes the unique current delimited segment. -/
theorem tupleHistory_succ {ι : Type} (L : ℕ) (kids : ι→List (List ℤ))
    (order : List ι) (done : ℕ) :
    tupleHistory L kids order (done+1)=
      tupleHistory L kids order done++tupleSegment L kids order (done+1) := by
  rw [tupleHistory_eq]
  rfl

/-- `lem:print`, paper/paper.tex: the initial
support state has exactly one empty tuple and only its real delimiter. -/
theorem tupleHistory_zero {ι : Type} (L : ℕ) (kids : ι→List (List ℤ)) (order : List ι) :
    tupleHistory L kids order 0=[false] := by
  simp [tupleHistory,tupleHistoryPrefix,tupleSegment,processedSupport,tupleFields_nil,fieldsRecs]

/-- `lem:print`, paper/paper.tex: completion
returns the literal full support, so the final suffix tuples are the
specified original-child Cartesian product. -/
theorem processedSupport_complete {ι : Type} (order : List ι) :
    processedSupport order order.length=order := by simp [processedSupport]

/-- `lem:print` and `prop:time`, paper/paper.tex: every partial tuple census pays only its actual
processed support exponent in the unchanged original child cap. -/
theorem processed_tuple_count_le {ι : Type} (kids : ι→List (List ℤ))
    (order : List ι) (done mc : ℕ) (hd : done≤order.length)
    (hk : ∀i∈order,(kids i).length≤ mc) :
    (tupleFields kids (processedSupport order done)).length≤ mc^done := by
  have h := tupleFields_length_le kids (processedSupport order done) mc (by
    intro i hi
    apply hk i
    exact List.mem_of_mem_drop hi)
  rw [processedSupport_length order done hd] at h
  exact h

end NearQuarticWires.StageTuple
