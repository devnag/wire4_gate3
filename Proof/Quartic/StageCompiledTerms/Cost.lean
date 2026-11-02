import Proof.Quartic.StageCompiledTerms.Machine
import Proof.Quartic.StageCompiledTerms.FrontCost
import Proof.Quartic.StageCompiledTerms.SelectedUnit
import Proof.Quartic.StageLiftSourceCost.Final

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the two
ordinary framed handoffs add the three actual component clocks. -/
theorem producer_clock_assembly (s f b S N U : ℕ)
    (hs : s≤5*S) (hf : f≤10000*N*U) (hb : b≤10^6*N*U) (hNU : 1≤N*U) :
    4*(4*s+4*(2*f+2)+12)+4*(2*b+2)+12≤80*S+10^9*N*U := by
  nlinarith only [hs,hf,hb,hNU]

/-- `prop:time`, paper/paper.tex: the once-only
raw-index polynomial adds to the selected column-times-polynomial cost. -/
theorem selected_cost_assembly (budget source calls K0 K1 T I : ℕ)
    (hbudget : budget≤80*source+10^9*calls)
    (hsource : source≤K0*(T+I)) (hcalls : calls≤K1*T) :
    budget≤(80*K0+10^9*K1)*(T+I) := by
  nlinarith only [hbudget,hsource,hcalls,Nat.zero_le (K1*I)]

/-- `prop:time`, paper/paper.tex: original
source processing is charged once; all following real streaming,
compiler, copy and cleanup work has one all-walk envelope factor. -/
theorem producerBudget_total_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    producerBudget r≤80*StageLift.sourceMachineBudget r+
      10^9*r.child.cellCall.seed.N^8*unitBudget r := by
  have hs:=framedSourceBudget_le r
  have hf:=actual_frontSteps_le r
  have hb:=compiledBatchSteps_le r
  have hn:=StageLiftSourceCost.walkCount_pos r
  have hu : 1≤unitBudget r := (sourcePacketBound_pos r).trans (sourcePacketBound_le_unit r)
  have hnu : 1≤r.child.cellCall.seed.N^8*unitBudget r:=Nat.mul_pos hn hu
  exact producer_clock_assembly (framedSourceBudget r) ((actualCarrier r).frontSteps)
    (compiledBatchSteps r) (StageLift.sourceMachineBudget r)
    (r.child.cellCall.seed.N^8) (unitBudget r) hs hf hb hnu

/-- `prop:time`, paper/paper.tex: the actual
complete original-input producer fits a fixed arity polynomial times
the selected column census, plus one additive raw-index polynomial.
The actual modular compiler census and original degree guard are unchanged. -/
theorem producerBudget_selected (B1 B2 : ℕ) :
    ∃ K e : ℕ,∀ r : Greedy.PrintRequest B1 B2,
      producerBudget r≤K*(2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e+
        ((Greedy.printIndexWord r).length+1)^e) := by
  obtain ⟨K0,e0,hsource⟩:=StageLiftSourceCost.sourceMachineBudget_selected B1 B2
  let E:=e0+unitExponent B1 B2+1
  refine ⟨80*K0+10^9*unitCoefficient B1 B2,E,?_⟩
  intro r
  let b:=r.child.call.n+1
  let I:=(Greedy.printIndexWord r).length+1
  let Z:=2^(r.child.call.n-r.child.selected.1.k)
  let T:=Z*b^E
  have hb : 1≤b := by dsimp [b];omega
  have hi : 1≤I := by dsimp [I];omega
  have he0 : e0≤E := by dsimp [E];omega
  have he1 : unitExponent B1 B2≤E := by dsimp [E];omega
  have hs : StageLift.sourceMachineBudget r≤K0*(T+I^E) :=
    (hsource r).trans (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb he0))
      (Nat.pow_le_pow_right hi he0)))
  have hu : r.child.cellCall.seed.N^8*unitBudget r≤unitCoefficient B1 B2*T := by
    calc _≤unitCoefficient B1 B2*Z*b^unitExponent B1 B2 := unitBudget_selected r
      _≤unitCoefficient B1 B2*Z*b^E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb he1)
      _=unitCoefficient B1 B2*T := Nat.mul_assoc _ _ _
  have hall:=producerBudget_total_le r
  have hall' : producerBudget r≤80*StageLift.sourceMachineBudget r+
      10^9*(r.child.cellCall.seed.N^8*unitBudget r) := by
    simpa only [Nat.mul_assoc] using hall
  exact selected_cost_assembly (producerBudget r) (StageLift.sourceMachineBudget r)
    (r.child.cellCall.seed.N^8*unitBudget r) K0 (unitCoefficient B1 B2) T (I^E) hall' hs hu

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: the exact original-input
compiled-Terms carrier has an actual ordinary machine at the required
sharp selected cost, with no packet, Formula, count or provider premise. -/
theorem costedCompiledTermsProducer (B1 B2 : ℕ) :
    ∃ K e : ℕ,Nonempty (WordFunction (Greedy.PrintRequest B1 B2) Greedy.printInput
      (fun r=>frame (StagePrint.TermsCarrier.word r))
      (fun r=>K*(2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e+
        ((Greedy.printIndexWord r).length+1)^e))) := by
  obtain ⟨K,e,hcost⟩:=producerBudget_selected B1 B2
  exact ⟨K,e,⟨(compiledTermsProducer B1 B2).2.enlargeBudget hcost⟩⟩

end NearQuarticWires.StageCompiledTerms
