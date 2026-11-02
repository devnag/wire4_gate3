import Proof.Quartic.StageFormulaMetadata.Machine
import Proof.Quartic.StageRecovery.OutputFrame

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageFormulaMetadata

/-- `lem:print` and `prop:time`, paper/paper.tex: the real formatter writes each output marker and
its final delimiter before the modular compiler's physical handoff. -/
noncomputable def framedFormatterBudget (request : ValidPacket) : ℕ :=
  finiteBudget StageRecovery.packetCallee VV MM request.val.word (3*request.steps+2)

/-- `lem:print`, paper/paper.tex: literal raw
postfix bytes are normalized and framed by one fixed ordinary machine;
no formatted request or formula is an additional input. -/
noncomputable def framedFormatterWordFunction :
    WordFunction ValidPacket (fun request=>request.val.word)
      (fun request=>frame request.output) framedFormatterBudget :=
  wordFunction_of_finite (fun request : ValidPacket=>request.val.word) (fun request=>frame request.output)
    StageRecovery.packetCallee (StageRecovery.OutputFrame.framedProgram formatterProgram)
    (fun request=>3*request.steps+2) (by
      intro request
      obtain ⟨b,n,he,hn,hout⟩:=formatterProgram_spec
        (finiteContext StageRecovery.packetCallee request.val.word)
        request.val (NearCubicGates.Close.Interfaces.Formats.toks request.formula)
        request.source request.mode rfl le_rfl
      have hf:=StageRecovery.OutputFrame.framedProgram_spec he
      have hzero : StageRecovery.OutputFrame.markedState (a0 : DS VV MM)=a0:=rfl
      rw [hzero] at hf
      change n≤request.steps at hn
      refine ⟨StageRecovery.OutputFrame.framedState b,3*n+2,hf,?_,by omega⟩
      change frame b.out=frame request.output
      rw [hout]
      rfl)

end NearQuarticWires.StageCompiledTerms
