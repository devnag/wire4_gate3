import Proof.Quartic.StagePrintTuple.Request
import Proof.Quartic.StagePrint.StackPrinter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: each actual
monomial uses precisely the ascending-support Cartesian list of its
ORIGINAL children after the same-phi native pullback. -/
def TermCutRequest.monomialTuples (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ) :
    List (List (List ℤ)) := tuples ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids)

/-- `lem:print`, paper/paper.tex: every actual
tuple contains one row per literal support variable, including the
single empty tuple for empty support. -/
theorem TermCutRequest.monomialTuples_length (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ)
    (rows : List (List ℤ)) (hr : rows ∈ r.monomialTuples t) :
    rows.length=t.1.card := by
  simpa only [List.length_map,Finset.length_sort] using
    mem_tuples_length ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids) rows hr

/-- `lem:print`, paper/paper.tex: every selected
native row has the exact common original-star coordinate count. -/
theorem TermCutRequest.monomialTuples_row_length (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ)
    (rows : List (List ℤ)) (hr : rows ∈ r.monomialTuples t)
    (row : List ℤ) (hrow : row ∈ rows) : row.length=r.rowDimension+1 := by
  obtain ⟨pool,hpool,hp⟩ := mem_tuples_mem
    ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids) rows hr row hrow
  obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hpool
  exact r.toRowContext.nativeKids_row_length i row hp

/-- `lem:print`, paper/paper.tex: all physically
flattened tuple fields satisfy the actual fixed signed source width. -/
theorem TermCutRequest.monomialTuples_fields_fit (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ) :
    ∀ x ∈ fieldNums ((r.monomialTuples t).map List.flatten),x<2^(r.stackWidth+1) := by
  intro x hx
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
  obtain ⟨flat,hflat,hz⟩ := List.mem_flatten.mp hz
  obtain ⟨rows,hrows,rfl⟩ := List.mem_map.mp hflat
  obtain ⟨row,hrow,hz⟩ := List.mem_flatten.mp hz
  obtain ⟨pool,hpool,hp⟩ := mem_tuples_mem
    ((t.1.sort (· ≤ ·)).map r.toRowContext.nativeKids) rows hrows row hrow
  obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hpool
  exact r.fields_fit i row hp z hz

/-- `lem:print`, paper/paper.tex: the actual
stacking request uses only the genuine tuple list and the monomial's
original signed coefficient; all machine preconditions follow from
the width-certified whole request. -/
def TermCutRequest.stackRequest (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ) (ht : t ∈ r.terms) :
    StagePrint.StackRequest where
  W := r.stackWidth
  s := r.rowDimension
  m := t.1.card
  tuples := r.monomialTuples t
  coefficient := t.2
  width_pos := r.width_pos
  tuple_length := r.monomialTuples_length t
  row_length := r.monomialTuples_row_length t
  fields_fit := r.monomialTuples_fields_fit t
  coefficient_fit := r.coefficient_fit t ht
  stack_fit := r.stack_fit t ht

/-- `lem:print`, paper/paper.tex: the genuine
stack-printer output is exactly the required equality-cut stream for
this monomial, with its sign and tuple order unchanged. -/
theorem TermCutRequest.stackRequest_output (r : TermCutRequest)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ) (ht : t ∈ r.terms) :
    (r.stackRequest t ht).output =
      (r.monomialTuples t).flatMap (cutRecs r.stackWidth r.rowDimension t.2) := rfl

end NearQuarticWires.StageTuple
