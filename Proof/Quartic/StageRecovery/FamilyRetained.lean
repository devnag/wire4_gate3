import Proof.Quartic.StageRecovery.FamilyFormatter
import Proof.Quartic.StageRecovery.FramedFamily
import Proof.Quartic.StageGamma.Retain
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: original-source
formatting and the single native family computation have additive
physical costs on disjoint ordinary machine banks. -/
noncomputable def FamilyCompileRequest.sourceFamilyBudget (r : FamilyCompileRequest) : ℕ :=
  4 * r.formatterBudget + 4 * (2 * familyFrameSteps r.family + 2) + 12

/-- `lem:print`, paper/paper.tex: the actual source
Formula and its paid metadata, rather than prepared setup tapes,
uniformly generate the complete original degree-bounded support family. -/
noncomputable def sourceFamilyWordFunction :
    WordFunction FamilyCompileRequest FamilyCompileRequest.word
      (fun r => frame r.family.output) FamilyCompileRequest.sourceFamilyBudget := by
  let g : WordFunction FamilyCompileRequest (fun r => r.family.word)
      (fun r => frame r.family.output) (fun r => 2 * familyFrameSteps r.family + 2) :=
    ⟨framedFamilyWordFunction.program, fun r => framedFamilyWordFunction.realizes r.family⟩
  exact Program.WordFunction.pipe familyFormatterWordFunction g

/-- `prop:time`, paper/paper.tex: retaining the original
source and appending the actual generated packet pays both complete
copies and exactly one source-to-family computation. -/
noncomputable def FamilyCompileRequest.retainedFamilyBudget (r : FamilyCompileRequest) : ℕ :=
  2 * (2 * r.sourceFamilyBudget + 150 * (r.word.length + r.family.output.length + 1)) + 2

/-- `lem:print`, paper/paper.tex: one genuine cold
ordinary machine preserves the original Formula source once and appends
the generated family. Its output still starts with the small structural
hint, with no support table or Formula values in its input. -/
noncomputable def retainedFamilyWordFunction :
    WordFunction FamilyCompileRequest FamilyCompileRequest.word
      (fun r => frame (r.word ++ r.family.output)) FamilyCompileRequest.retainedFamilyBudget :=
  StageGamma.retainedWordFunction sourceFamilyWordFunction

end NearQuarticWires.StageRecovery
