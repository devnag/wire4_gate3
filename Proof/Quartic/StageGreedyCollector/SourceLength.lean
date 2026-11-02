import Proof.Quartic.StageGreedyCollector.ContextTarget
import Proof.Quartic.StageCompiledTerms.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open StageCompiledTerms

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual compiled carrier's length is controlled by
the real all-walk compiler stage, independently of raw target-index
acquisition before that stage. -/
theorem carrier_length_selected (B1 B2 : ℕ) : ∃K e : ℕ,
    ∀r : Greedy.PrintRequest B1 B2,
      (StagePrint.TermsCarrier.word r).length+1≤
        K*2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e := by
  refine ⟨3*10^6*unitCoefficient B1 B2,unitExponent B1 B2,fun r=>?_⟩
  have ho:=Control.output_length_le (compiledBatchWordFunction B1 B2) r
  change (frame (StagePrint.TermsCarrier.word r)).length≤2*compiledBatchSteps r+2+1 at ho
  rw [frame_length] at ho
  have hb:=compiledBatchSteps_le r
  have hN:=StageLiftSourceCost.walkCount_pos r
  have hU : 1≤unitBudget r := (sourcePacketBound_pos r).trans (sourcePacketBound_le_unit r)
  have hNU : 1≤r.child.cellCall.seed.N^8*unitBudget r := Nat.mul_pos hN hU
  have hl : (StagePrint.TermsCarrier.word r).length+1≤
      3*10^6*(r.child.cellCall.seed.N^8*unitBudget r) := by nlinarith only [ho,hb,hNU]
  calc
    _≤3*10^6*(r.child.cellCall.seed.N^8*unitBudget r) := hl
    _≤3*10^6*(unitCoefficient B1 B2*2^(r.child.call.n-r.child.selected.1.k)*
        (r.child.call.n+1)^unitExponent B1 B2) := Nat.mul_le_mul_left _ (unitBudget_selected r)
    _=_ := by ring

/-- `prop:time`, paper/paper.tex: a real
linear carrier pass with fixed original-arity overhead fits the same
selected column budget, with no additive raw-index term. -/
theorem context_budget_selected {B1 B2 : ℕ} {budget : Greedy.PrintRequest B1 B2→ℕ}
    (hb : ContextBudgetBound budget) : ∃K e : ℕ,∀r,
      budget r≤K*2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e := by
  obtain ⟨C,E,hC⟩:=hb
  obtain ⟨K,e,hK⟩:=carrier_length_selected B1 B2
  refine ⟨C*K,E+e,fun r=>?_⟩
  calc
    budget r≤C*(r.child.call.n+1)^E*((StagePrint.TermsCarrier.word r).length+1) := hC r
    _≤C*(r.child.call.n+1)^E*(K*2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e) :=
      Nat.mul_le_mul_left _ (hK r)
    _=_ := by rw [pow_add];ring

end NearQuarticWires.StageGreedyCollector
