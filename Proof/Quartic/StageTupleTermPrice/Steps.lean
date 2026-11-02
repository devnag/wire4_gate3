import Proof.Quartic.StageTupleTermPrice.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open StageTuple

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual reverse iteration selects exactly its next
support atom and current original-child suffix tuple segment. -/
structure Step where
  monomial : Case
  done : ℕ
  done_lt : done< monomial.order.length

def Step.small (j : Step) : ℕ:=j.monomial.small

def Step.atom (j : Step) :=j.monomial.order[
  (reverseSupportIndex j.monomial.order j.done j.done_lt).val]

def Step.supportRequest (j : Step) : SupportIndexRequest:=
  finiteSupportRequest j.monomial.order (reverseSupportIndex j.monomial.order j.done j.done_lt)

def Step.nativeRequest (j : Step) : StageNativeKids.NativeKidsRequest:=
  StageNativeKids.NativeKidsRequest.ofTerm j.monomial.request j.atom

def Step.tupleRequest (j : Step) : StagePrint.ChildTupleRequest:=
  j.monomial.request.toRowContext.tupleStepRequest j.monomial.width (by unfold Case.width;omega)
    j.atom (processedSupport j.monomial.order j.done)

def Step.square (j : Step) : ℕ:=
  (j.tupleRequest.children.length+1)^2*(j.tupleRequest.tuples.length+1)^2

theorem Step.small_pos (j : Step) : 1≤ j.small:=j.monomial.small_pos

theorem Step.done_le_small (j : Step) : j.done≤ j.small := by
  have hh:=j.done_lt
  rw [j.monomial.order_length] at hh
  exact hh.le.trans j.monomial.card_le_small

theorem Step.child_count (j : Step) : j.tupleRequest.children.length≤ j.monomial.childCap :=
  j.monomial.children_le j.atom

theorem Step.tuple_count (j : Step) : j.tupleRequest.tuples.length≤ j.monomial.childCap^j.done := by
  exact processed_tuple_count_le _ _ _ _ j.done_lt.le (fun i _=> j.monomial.children_le i)

theorem Step.dimensions (j : Step) :
    j.tupleRequest.L≤ j.small ∧ j.tupleRequest.N≤ j.small ∧
    j.tupleRequest.M≤ j.small^2 := by
  have hd:=j.done_le_small
  have hn:=j.monomial.small_bounds.2.2.2.1
  change j.monomial.request.rowDimension+1≤j.small at hn
  have hl:=j.monomial.small_bounds.2.2.1
  have hlen:=processedSupport_length j.monomial.order j.done j.done_lt.le
  refine ⟨hl,hn,?_⟩
  change (processedSupport j.monomial.order j.done).length*(j.monomial.request.rowDimension+1)≤_
  rw [hlen]
  nlinarith only [hd,hn]

theorem Step.square_pos (j : Step) : 1≤ j.square := by
  have h1 : 1≤(j.tupleRequest.children.length+1)^2:=Nat.one_le_pow _ _ (by omega)
  have h2 : 1≤(j.tupleRequest.tuples.length+1)^2:=Nat.one_le_pow _ _ (by omega)
  exact Nat.mul_le_mul h1 h2

/-- `prop:time`, paper/paper.tex: the
real child/old-tuple square at every proper reverse step consumes
only the square census of this actual support. -/
theorem Step.square_bound (j : Step) :
    j.square≤16*j.monomial.childCap^(2*j.monomial.card) := by
  have hmc:=j.monomial.childCap_pos
  have hk:=j.child_count
  have ht:=j.tuple_count
  have hpow : 1≤ j.monomial.childCap^j.done:=Nat.one_le_pow _ _ hmc
  have hK : j.tupleRequest.children.length+1≤2*j.monomial.childCap := by omega
  have hT : j.tupleRequest.tuples.length+1≤2*j.monomial.childCap^j.done := by omega
  have hh:=Nat.mul_le_mul (Nat.pow_le_pow_left hK 2) (Nat.pow_le_pow_left hT 2)
  have hd:=j.done_lt
  rw [j.monomial.order_length] at hd
  calc
    _≤(2*j.monomial.childCap)^2*(2*j.monomial.childCap^j.done)^2 := hh
    _=16*(j.monomial.childCap^2*(j.monomial.childCap^j.done)^2) := by ring
    _=16*j.monomial.childCap^(2+j.done*2) := by rw [←pow_mul,←pow_add]
    _=16*j.monomial.childCap^(2*(j.done+1)) := by congr 1;congr 1;omega
    _≤_ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hmc (by omega))

end NearQuarticWires.StageTupleTermPrice
