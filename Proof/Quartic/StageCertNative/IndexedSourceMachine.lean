import Proof.Quartic.StageCertNative.IndexedSourceBody
import Proof.Quartic.StageFormulaMetadata.FiniteMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageCert.Tokens

noncomputable def indexedSourceBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM (indexedMomentWord r)
    (3*indexedSourceSteps r+8)

/-- `lem:print` and `prop:time`, paper/paper.tex: a counted loop's literal prefix-index source is
physically converted to the existing complete signed source request.
The measured-source allocator and every frame/copy are charged. -/
noncomputable def indexedSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) indexedMomentWord
      (fun r=>frame r.word) indexedSourceBudget :=
  StageFormulaMetadata.wordFunction_of_finite indexedMomentWord (fun r=>frame r.word)
    StageRecovery.packetCallee indexedSourceProgram (fun r=>3*indexedSourceSteps r+8)
    (fun r=>by
      obtain ⟨b,n,he,hn,ho⟩:=indexedSourceProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee (indexedMomentWord r)) r rfl
        (by change r.word.length+4≤100*((indexedMomentWord r).length+1)
            rw [indexedMomentWord_length];omega)
      exact ⟨b,n,he,ho,hn⟩)

/-- `lem:print`, paper/paper.tex: the actual
prefix-indexed source feeds the original signed mask, moment and
exact-format computation without changing any witness or test. -/
noncomputable def indexedFormattedSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) indexedMomentWord
      (fun r=>frame r.validPacket.output)
      (fun r=>4*indexedSourceBudget r+4*r.framedSourceBudget+12) :=
  Program.WordFunction.pipe (indexedSourceWordFunction B1 B2)
    (momentFramedSourceWordFunction B1 B2)

end NearQuarticWires.StageCertNative
