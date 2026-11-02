import Proof.Quartic.StageTupleTermPrice.Codecs
import Proof.Quartic.StageTupleTermPrice.Records
import Proof.Quartic.StageTupleTermPrice.FinishTarget

set_option autoImplicit false

namespace NearQuarticWires.StageTupleFinishPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open StageTuple StageTupleTermPrice

/-- `lem:print`, paper/paper.tex: the final
Stack request contains precisely the actual current monomial's signed
coefficient and its original ordered child tuples. -/
def stack (j : Case) : StagePrint.StackRequest :=
  j.request.stackRequest j.term j.term_mem

/-- `prop:time`, paper/paper.tex: every actual
Stack dimension is bounded by the original structural magnitude,
independently of the whole Terms source and earlier output/history. -/
theorem stack_dimensions (j : Case) :
    (stack j).W≤j.small ∧ (stack j).s≤j.small ∧ (stack j).m≤j.small := by
  have hw:=j.small_bounds.2.2.1
  have hs:=j.small_bounds.2.2.2.1
  have hm:=j.card_le_small
  change j.request.stackWidth+1≤j.small at hw
  change j.request.rowDimension+1≤j.small at hs
  change j.request.stackWidth≤j.small ∧ j.request.rowDimension≤j.small ∧ j.card≤j.small
  omega

/-- `prop:time`, paper/paper.tex: the genuine
final tuple count is at most the original child cap to the actual
support cardinal, including empty support and zero-child pools. -/
theorem stack_tuples_le (j : Case) : (stack j).tuples.length≤j.childCap^j.card := by
  have h:=tupleFields_length_le j.request.toRowContext.nativeKids j.order j.childCap
    (fun i _=>j.children_le i)
  simpa only [tupleFields,List.length_map,Finset.length_sort,Case.card,Case.order,stack,
    TermCutRequest.stackRequest,TermCutRequest.monomialTuples] using h

/-- `prop:time`, paper/paper.tex: adding the
empty-case overhead costs at most twice the actual support census. -/
theorem stack_tuples_add_one (j : Case) :
    (stack j).tuples.length+1≤2*j.childCap^j.card := by
  have h:=stack_tuples_le j
  have hp : 1≤j.childCap^j.card:=Nat.one_le_pow _ _ j.childCap_pos
  omega

/-- `prop:time`, paper/paper.tex: the real
quadratic Stack factor has exactly twice the original actual support
exponent, with a fixed factor four for empty and zero-child cases. -/
theorem stack_tuples_square (j : Case) :
    ((stack j).tuples.length+1)^2≤4*j.childCap^(2*j.card) := by
  calc
    _≤(2*j.childCap^j.card)^2 := Nat.pow_le_pow_left (stack_tuples_add_one j) 2
    _=_ := by rw [mul_pow,←pow_mul,Nat.mul_comm j.card 2];rfl

/-- `prop:time`, paper/paper.tex: a linear
current tuple-count factor is also bounded by the same square census,
without introducing another support exponent. -/
theorem stack_tuples_square_census (j : Case) :
    (stack j).tuples.length+1≤2*j.childCap^(2*j.card) := by
  refine (stack_tuples_add_one j).trans (Nat.mul_le_mul_left 2 ?_)
  exact Nat.pow_le_pow_right j.childCap_pos (by omega)

end NearQuarticWires.StageTupleFinishPrice
