import Proof.Quartic.StageNativeKidsPoolPrice.Rows

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPoolPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open StageNativeKids StageNativeKidsPrice StageNativeKidsPool StageTuple StagePrint
open scoped BigOperators

/-- `prop:time`, paper/paper.tex: the
literal sum of every real original-child occurrence clock has one
structural polynomial price, including the empty original pool. -/
theorem step_price : Price SourceCase.scale
    (fun a=>(actualFamily a).stepBudget OriginalPipelineRequest.budget) := by
  obtain ⟨K,e,he⟩:=occurrence_price
  have hc:=count_price
  have hs:=Price.identity SourceCase.scale
  have h : Price SourceCase.scale (fun a=>(actualFamily a).count*(K*a.scale^e)) := by
    price_with scale_pos
  apply h.mono
  intro a
  simp only [Family.stepBudget,List.sum_ofFn]
  calc
    _ ≤ ∑ j : Fin (actualFamily a).count,K*a.scale^e := by
      apply Finset.sum_le_sum
      intro j _
      exact he (RowCase.mk a j)
    _ = _ := by simp

end NearQuarticWires.StageNativeKidsPoolPrice
