import Proof.Quartic.StageCertNative.CountedSourceBody
import Proof.Quartic.StageCertNative.FramedTerms

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

noncomputable def jobSourceBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  StageFormulaMetadata.finiteBudget StageRecovery.packetCallee VV MM r.word
    (3*countedSourceSteps r.moment (termCount r.base)+8)

/-- `lem:print`, paper/paper.tex: the actual
once-context loop input produces the original complete signed source
request. The shared context remains source data, not a supplied pool,
Formula or per-entry table. -/
noncomputable def jobSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word (fun r=>frame r.moment.word) jobSourceBudget :=
  StageFormulaMetadata.wordFunction_of_finite TermJob.word (fun r=>frame r.moment.word)
    StageRecovery.packetCallee countedSourceProgram
    (fun r=>3*countedSourceSteps r.moment (termCount r.base)+8) (fun r=>by
      obtain ⟨b,n,he,hn,ho⟩:=countedSourceProgram_run
        (StageFormulaMetadata.finiteContext StageRecovery.packetCallee r.word) r rfl
        (by change r.word.length+4≤100*(r.word.length+1);omega)
      exact ⟨b,n,he,ho,hn⟩)

noncomputable def suffixFormulaBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*r.framedSourceBudget+4*projectionBudget r+12

noncomputable def suffixFormulaWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>frame (formulaWord ⟨r.packet.arity,r.formula⟩)) suffixFormulaBudget :=
  Program.WordFunction.pipe (momentFramedSourceWordFunction B1 B2) (projectionWordFunction B1 B2)

noncomputable def suffixTermsBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*suffixFormulaBudget r+4*(2*expandFrameSteps NearCubicGates.Close.Expand.expansionMachine
    ⟨r.packet.arity,r.formula⟩+2)+12

noncomputable def suffixTermsWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>frame (termsWord (exactTerms r))) suffixTermsBudget :=
  Program.WordFunction.pipe (suffixFormulaWordFunction B1 B2)
    (restrictWordFunction (framedExpandWordFunction NearCubicGates.Close.Expand.expansionMachine)
      (fun r : MomentRequest B1 B2=>⟨r.packet.arity,r.formula⟩))

noncomputable def jobTermsBudget {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  4*jobSourceBudget r+4*suffixTermsBudget r.moment+12

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual term in the once-context source loop
produces its literal exact expanded Terms by fixed physical source,
formatter, projection, expansion and counted-codec framing machines.
All original witness bits, signs and failed columns are preserved. -/
noncomputable def jobTermsWordFunction (B1 B2 : ℕ) :
    WordFunction (TermJob B1 B2) TermJob.word
      (fun r=>frame (termsWord (exactTerms r.moment))) jobTermsBudget :=
  Program.WordFunction.pipe (jobSourceWordFunction B1 B2)
    (restrictWordFunction (suffixTermsWordFunction B1 B2) (fun r : TermJob B1 B2=>r.moment))

end NearQuarticWires.StageCertNative
