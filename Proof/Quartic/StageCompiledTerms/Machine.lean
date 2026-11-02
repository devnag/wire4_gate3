import Proof.Quartic.StageCompiledTerms.FramedSource
import Proof.Quartic.StageCompiledTerms.FrontendMachine
import Proof.Quartic.StageCompiledTerms.Batch

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary

/-- Step 3 and `prop:time`, paper/paper.tex: the real complete budget is additive in original
source synthesis, one streaming adaptation and all modular calls. -/
noncomputable def producerBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  4*(4*framedSourceBudget r+4*(2*(actualCarrier r).frontSteps+2)+12)+
    4*(2*compiledBatchSteps r+2)+12

/-- Step 3 and `lem:print`, paper/paper.tex: the complete actual producer starts with literal
Greedy.printInput, retains one original preparation and emits every
original low-first indexed compiled-Terms entry, including zero walks.
All source, normalization, compiler, copy and reset programs execute. -/
noncomputable def compiledTermsProducer (B1 B2 : ℕ) : StagePrint.TermsCarrier.Producer B1 B2 := by
  let adapt : WordFunction (Greedy.PrintRequest B1 B2) StageLift.sourceCarrierWord
      (fun r=>frame (actualCarrier r).batchWord) (fun r=>2*(actualCarrier r).frontSteps+2) :=
    ⟨carrierFrontendWordFunction.program,fun r=>by
      have hr:=carrierFrontendWordFunction.realizes (actualCarrier r)
      rw [actualCarrier_word] at hr
      exact hr⟩
  exact ⟨producerBudget,Program.WordFunction.pipe
    (Program.WordFunction.pipe (framedSourceWordFunction B1 B2) adapt)
    (compiledBatchWordFunction B1 B2)⟩

end NearQuarticWires.StageCompiledTerms
