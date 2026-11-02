import Proof.Gates.TabMachine.Tuple

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the exact
ordered Cartesian child tuples are stored as concatenated signed rows. -/
def tupleFields {ι : Type} (kids : ι → List (List ℤ)) (order : List ι) : List (List ℤ) :=
  (tuples (order.map kids)).map List.flatten

/-- `lem:print`, paper/paper.tex: empty support
has one empty tuple, rather than zero tuples, even though it has no fields. -/
theorem tupleFields_nil {ι : Type} (kids : ι → List (List ℤ)) :
    tupleFields kids [] = [[]] := rfl

/-- `lem:print`, paper/paper.tex: the actual child
machine's prepend step preserves the precise lexicographic tuple order. -/
theorem tupleFields_cons {ι : Type} (kids : ι → List (List ℤ)) (i : ι) (order : List ι) :
    tupleFields kids (i :: order) = newT (kids i) (tupleFields kids order) :=
  tuples_flatten (kids i) (order.map kids)

/-- `lem:print`, paper/paper.tex: building child
fields last-to-first is exactly the finite Cartesian specification. -/
theorem tupleFields_foldr {ι : Type} (kids : ι → List (List ℤ)) (order : List ι) :
    order.foldr (fun i current => newT (kids i) current) [[]] = tupleFields kids order := by
  induction order with
  | nil => rfl
  | cons i order ih => rw [List.foldr_cons, ih, tupleFields_cons]

/-- `lem:print`, paper/paper.tex: a sequential
controller processes the physical support list in reverse to retain the
specified ascending-support lexicographic Cartesian output order. -/
theorem tupleFields_reverse_foldl {ι : Type} (kids : ι → List (List ℤ)) (order : List ι) :
    order.reverse.foldl (fun current i => newT (kids i) current) [[]] = tupleFields kids order := by
  simpa only [List.foldr_eq_foldl_reverse] using tupleFields_foldr kids order

/-- `lem:print`, paper/paper.tex: actual tuple
census is the product of the original child-list lengths, preserving
zero-child atoms and duplicate occurrence positions. -/
theorem tupleFields_length {ι : Type} (kids : ι → List (List ℤ)) (order : List ι) :
    (tupleFields kids order).length = (order.map (fun i => (kids i).length)).prod := by
  simp only [tupleFields, List.length_map, tuples_length, List.map_map]
  rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: every partial tuple bank has the sharp original-child
census power at its actual processed support length. -/
theorem tupleFields_length_le {ι : Type} (kids : ι → List (List ℤ)) (order : List ι)
    (mc : ℕ) (hk : ∀ i ∈ order, (kids i).length ≤ mc) :
    (tupleFields kids order).length ≤ mc ^ order.length := by
  rw [tupleFields_length]
  induction order with
  | nil => simp
  | cons i order ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have hi := hk i (by simp)
    have ht := ih (fun j hj => hk j (by simp [hj]))
    simpa only [Nat.mul_comm] using Nat.mul_le_mul hi ht

/-- `lem:print`, paper/paper.tex: a zero-child
atom produces no tuples; it does not become the singleton empty tuple. -/
theorem tupleFields_eq_nil_of_empty {ι : Type} (kids : ι → List (List ℤ))
    (order : List ι) (i : ι) (hi : i ∈ order) (he : kids i = []) :
    tupleFields kids order = [] := by
  induction order with
  | nil => simp at hi
  | cons j order ih =>
    rw [tupleFields_cons]
    rcases List.mem_cons.mp hi with hij | hi
    · subst j
      simp [he, newT]
    · rw [ih hi]
      simp [newT]

end NearQuarticWires.StageTuple
