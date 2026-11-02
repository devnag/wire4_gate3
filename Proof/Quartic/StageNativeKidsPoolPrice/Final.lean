import Proof.Quartic.StageNativeKidsPoolPrice.StepSum
import Proof.Quartic.StageNativeKidsPoolPrice.Streams
import Proof.Quartic.StageNativeKidsPoolPrice.FixedCosts

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPoolPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open StageNativeKids StageNativeKidsPrice StageNativeKidsPool StageTuple StagePrint

/-- `prop:time`, paper/paper.tex: the
unchanged complete actual pool clock has a structural polynomial price,
including its literal per-occurrence sum, counter, output and framing. -/
theorem budget_price : Price SourceCase.scale (fun a=>actualPoolBudget a) := by
  have hl:=loader_price
  have hcopy:=counter_copy_price
  have hcount:=StageNativeKidsPrice.count_price
  have hi:=initialize_price
  have hc:=count_price
  have hs:=step_price
  have ho:=answer_price
  simp only [actualPoolBudget,actualPoolSteps]
  price_with scale_pos

/-- `prop:time`, paper/paper.tex: both
actual original-bank cases satisfy the exact frozen pool price target
without an external price, width, count, row, cap or caller premise. -/
theorem actualPoolPrice : StageNativeKidsPool.ActualPoolPrice := budget_price

/-- `prop:time`, paper/paper.tex: the
actual first and second ordinary pool clocks have the SAME fixed
coefficient and exponent at their original request resource. -/
theorem poolBudgets_polynomial : ∃ K e : ℕ,
    (∀ q : FirstBankRequest,firstPoolBudget q ≤ K*q.val.originalSourceScale^e) ∧
    (∀ q : SecondBankRequest,secondPoolBudget q ≤ K*q.val.originalSourceScale^e) := by
  obtain ⟨K,e,he⟩:=actualPoolPrice
  exact ⟨K,e,(fun q=>he ⟨q.val,false,q.property⟩),(fun q=>he ⟨q.val,true,q.property⟩)⟩

end NearQuarticWires.StageNativeKidsPoolPrice
