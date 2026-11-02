import Proof.Quartic.StageTupleFinishPrice.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTupleFinishPrice

open StageTuple StageTupleTermPrice

/-- `prop:time`, paper/paper.tex: the genuine
complete ordinary Stack clock keeps exactly the square census of the
actual monomial support, with fixed original structural constants. -/
theorem stack_selected : ∃C E : ℕ,1≤C ∧ 1≤E ∧ ∀j : Case,
    2*(stack j).budget+2≤C*j.small^E*j.childCap^(2*j.card) := by
  obtain ⟨K,E,hK,hE,h⟩:=StageTupleCensusBounds.stackCostBound
  refine ⟨4*K*4^E,E,?_,hE,fun j=>?_⟩
  · have hp : 1≤(4:ℕ)^E:=Nat.one_le_pow _ _ (by decide)
    nlinarith
  · obtain ⟨hW,hs,hm⟩:=stack_dimensions j
    have hp:=j.small_pos
    calc
      _≤K*((stack j).W+(stack j).s+(stack j).m+1)^E*
          ((stack j).tuples.length+1)^2 := h (stack j)
      _≤K*(4*j.small)^E*(4*j.childCap^(2*j.card)) := by
        gcongr
        · omega
        · exact stack_tuples_square j
      _=_ := by rw [mul_pow];ring

end NearQuarticWires.StageTupleFinishPrice
