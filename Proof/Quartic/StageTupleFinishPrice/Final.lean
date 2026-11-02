import Proof.Quartic.StageTupleFinishPrice.Input
import Proof.Quartic.StageTupleFinishPrice.Caches
import Proof.Quartic.StageTupleFinishPrice.Stack

set_option autoImplicit false

namespace NearQuarticWires.StageTupleFinishPrice

open StageTuple StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: the frozen
finish magnitude is exactly the actual formatter/source sizes, genuine
ordinary Stack budget and three finite current-monomial caches. -/
theorem magnitude_eq (j : Case) :
    monomialFinishMagnitude j.request (j.request.progressMonomial j.index j.index_lt)
      j.term j.term_mem=
    stackInputMagnitude (stack j)+(stack j).word.length+
      (2*(stack j).budget+2)+cacheSize j := by
  unfold monomialFinishMagnitude cacheSize stack
  dsimp only
  ring

/-- `prop:time`, paper/paper.tex: the exact
actual final Stack, source formatting and finite cleanup clock has a
fixed structural polynomial times the square census of the actual
support, with no earlier Terms/output/history or supplier premise. -/
theorem finishCostBound : StageTupleTermPrice.FinishCostBound := by
  obtain ⟨K,E,hK,hE,hstack⟩:=stack_selected
  refine ⟨100000000*(3300+K),E+4,by omega,by omega,fun j=>?_⟩
  have h4:=Nat.pow_le_pow_right j.small_pos (show 4≤E+4 by omega)
  have he:=Nat.pow_le_pow_right j.small_pos (show E≤E+4 by omega)
  have hi : stackInputMagnitude (stack j)+(stack j).word.length≤
      3200*j.small^(E+4)*j.childCap^(2*j.card) := by
    refine (input_size_selected j).trans ?_
    gcongr
  have hc : cacheSize j≤100*j.small^(E+4)*j.childCap^(2*j.card) := by
    refine (caches_selected j).trans ?_
    gcongr
  have hs : 2*(stack j).budget+2≤K*j.small^(E+4)*j.childCap^(2*j.card) := by
    refine (hstack j).trans ?_
    gcongr
  rw [magnitude_eq]
  calc
    _≤100000000*((3300+K)*j.small^(E+4)*j.childCap^(2*j.card)) := by
      apply Nat.mul_le_mul_left
      nlinarith only [hi,hc,hs]
    _=_ := by ring

end NearQuarticWires.StageTupleFinishPrice
