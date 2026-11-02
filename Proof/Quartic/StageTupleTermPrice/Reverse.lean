import Proof.Quartic.StageTupleTermPrice.Cartesian
import Proof.Quartic.StageTupleTermPrice.NativePhase
import Proof.Quartic.StageTupleTermPrice.Cleanup

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires
open StageTuple StageNativeKids

/-- `lem:print`, paper/paper.tex: the
literal actual monomial data use this source's current Terms boundary,
original signed coefficient and actual sorted support. -/
def Case.data (j : Case) :=j.request.progressMonomial j.index j.index_lt

noncomputable def Step.cost (j : Step) : ℕ:=
  reverseStepCost NativeKidsRequest.budget j.monomial.request j.monomial.data j.done j.done_lt

/-- `prop:time`, paper/paper.tex: the
four genuine reverse phases and their sequence transitions preserve
the same actual separate child/suffix-tuple square. -/
theorem price_reverseStep : WeightedPrice Step.small Step.square Step.cost := by
  have h1:=WeightedPrice.of_price Step.square_pos (Price.constant Step.small 1)
  have hs:=WeightedPrice.of_price Step.square_pos price_supportPhase
  have hn:=WeightedPrice.mul_small (Price.constant Step.small 1000000) price_nativePhase
  have hcleanup:=(price_counters.add Step.small_pos h1).add Step.small_pos price_cleanup
  have hcart:=(price_cartesianStep.add Step.small_pos h1).add Step.small_pos hcleanup
  have hnative:=(hn.add Step.small_pos h1).add Step.small_pos hcart
  exact (hs.add Step.small_pos h1).add Step.small_pos hnative

private theorem finite_sum_bound {T : ℕ} (f : Fin T→ℕ) (H : ℕ)
    (h : ∀i,f i≤H) : (List.ofFn f).sum≤T*H := by
  have hh:=List.sum_le_card_nsmul (List.ofFn f) H (by
    intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact h i)
  simpa only [List.length_ofFn,smul_eq_mul] using hh

def Case.weight (j : Case) : ℕ:=j.childCap^(2*j.card)

theorem Case.weight_pos (j : Case) : 1≤j.weight:=Nat.one_le_pow _ _ j.childCap_pos

/-- `prop:time`, paper/paper.tex: the
actual reverse loop sums its real iteration costs and then pays the
existing support-length multiplier. Only structural support powers
are added; the child exponent remains twice the actual support card. -/
theorem price_reverseLoop : WeightedPrice Case.small Case.weight
    (fun j=>reverseLoopCost NativeKidsRequest.budget j.request j.data) := by
  obtain ⟨C,E,h⟩:=price_reverseStep
  refine ⟨16*C+5,E+2,fun j=>?_⟩
  have hstep (i : Fin j.order.length) :
      reverseStepCost NativeKidsRequest.budget j.request j.data i.val i.isLt≤
        16*C*j.small^E*j.weight := by
    let s : Step:=⟨j,i.val,i.isLt⟩
    have hc:=h s
    have hq:=s.square_bound
    calc
      _≤C*j.small^E*s.square := hc
      _≤C*j.small^E*(16*j.weight) := Nat.mul_le_mul_left _ hq
      _=_ := by ring
  have hsum:=finite_sum_bound
    (fun i : Fin j.order.length=>reverseStepCost NativeKidsRequest.budget j.request j.data i.val i.isLt)
    (16*C*j.small^E*j.weight) hstep
  have hloop:=Nat.mul_le_mul_left j.order.length hsum
  have ha : j.order.length≤j.small:=j.order_length.trans_le j.card_le_small
  have hs:=j.small_pos
  have hw:=j.weight_pos
  have ha2:=Nat.pow_le_pow_left ha 2
  have hlead:=Nat.mul_le_mul_right (16*C*j.small^E*j.weight) ha2
  have heq : j.small^(E+2)=j.small^E*j.small^2 := pow_add _ _ _
  have hsmall : j.small≤j.small^(E+2)*j.weight :=
    (Nat.le_self_pow (by omega : E+2≠0) _).trans (Nat.le_mul_of_pos_right _ (by omega))
  have hone : 1≤j.small^(E+2)*j.weight:=Nat.mul_le_mul
    (Nat.one_le_pow _ _ hs) hw
  change j.order.length*((List.ofFn fun i : Fin j.order.length=>
    reverseStepCost NativeKidsRequest.budget j.request j.data i.val i.isLt).sum+4)+1≤_
  rw [heq]
  rw [heq] at hsmall hone
  nlinarith only [hloop,hlead,hsmall,hone,ha]

end NearQuarticWires.StageTupleTermPrice
