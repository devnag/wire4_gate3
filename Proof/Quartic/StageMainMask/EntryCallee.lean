import Proof.Quartic.StageMainMask.StructuralFinal
import Proof.Quartic.StageMainMask.PredicateFramed
import Proof.Quartic.StageMainPopulation.Cost
import Proof.Quartic.StageMain.TaggedWordFunction

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
one fixed ordinary selector handles the actual original population and
complete predicate requests with independent physical tape banks. -/
noncomputable def populationPredicateMachine :
    WordFunction (PopulationRequest ⊕ PredicateRequest)
      (Tagged.taggedInput PopulationRequest.word PredicateRequest.word)
      (fun r => frame (Tagged.taggedAnswer (fun p : PopulationRequest => natWord p.value)
        (fun p : PredicateRequest => [p.value]) r))
      (Tagged.taggedCost PopulationRequest.word (fun p => natWord p.value)
        PredicateRequest.word (fun p => [p.value]) StageMainPopulation.populationBudget
        (fun p => framedPredicateBudget p.word.length)) :=
  Tagged.taggedWordFunction StageMainPopulation.populationWordFunction framedPredicateMachine

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the three actual cold subroutines
share one uniform ordinary call port, with every selector and physical
bank copy included in its exact per-request budget. -/
noncomputable def entryCallee (B1 B2 : ℕ) : Callee where
  Req := StructuralRequest B1 B2 ⊕ (PopulationRequest ⊕ PredicateRequest)
  inw := Tagged.taggedInput structuralWord
    (Tagged.taggedInput PopulationRequest.word PredicateRequest.word)
  outw := fun r => frame (Tagged.taggedAnswer (fun p => [structuralBit p])
    (Tagged.taggedAnswer (fun p : PopulationRequest => natWord p.value)
      (fun p : PredicateRequest => [p.value])) r)
  bud := Tagged.taggedCost structuralWord (fun p => [structuralBit p])
    (Tagged.taggedInput PopulationRequest.word PredicateRequest.word)
    (Tagged.taggedAnswer (fun p : PopulationRequest => natWord p.value)
      (fun p : PredicateRequest => [p.value])) structuralBudget
    (Tagged.taggedCost PopulationRequest.word (fun p => natWord p.value)
      PredicateRequest.word (fun p => [p.value]) StageMainPopulation.populationBudget
      (fun p => framedPredicateBudget p.word.length))
  wf := Tagged.taggedWordFunction (structuralWordFunction B1 B2) populationPredicateMachine

end NearQuarticWires.StageMainMask
