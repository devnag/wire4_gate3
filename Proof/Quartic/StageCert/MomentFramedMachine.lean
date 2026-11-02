import Proof.Quartic.StageCert.MomentFormattedPrice

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageFormulaMetadata

/-- `lem:print`, paper/paper.tex: physical
framing preserves the entire exact signed formatted stream for the
ordinary whole-test term loop. -/
def framedMomentFormatter : St VV MM :=
  StageMain.framedOutputProgram formatterProgram

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual formatter run, with both postfix scans,
is transformed into a literal outer-framed run without an output oracle. -/
theorem framedMomentFormatter_run {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    ∃ b n,
      Ex (finiteContext StageRecovery.packetCallee r.packet.word) framedMomentFormatter a0 b n ∧
      b.out=frame r.validPacket.output ∧ n≤3*r.validPacket.steps+2 := by
  let v := r.validPacket
  obtain ⟨b,n,he,hn,ho⟩ := formatterProgram_spec
    (finiteContext StageRecovery.packetCallee v.val.word) v.val
    (NearCubicGates.Close.Interfaces.Formats.toks v.formula) v.source v.mode rfl le_rfl
  have hm : StageMain.markOutputState (a0 : DS VV MM)=a0 := rfl
  have hf := StageMain.framedOutput_run he
  rw [hm] at hf
  change n≤r.validPacket.steps at hn
  refine ⟨{b with out:=frame b.out},3*n+2,hf,?_,by omega⟩
  change frame b.out=frame v.output
  exact congrArg frame ho

/-- `prop:time`, paper/paper.tex: the framed
formatter's clock includes the same finite-source allocation and
ordinary compilation, with its actual marked-output work. -/
noncomputable def MomentRequest.framedFormatterBudget {B1 B2 : ℕ}
    (r : MomentRequest B1 B2) : ℕ :=
  finiteBudget StageRecovery.packetCallee VV MM r.packet.word (3*r.validPacket.steps+2)

/-- `lem:print`, paper/paper.tex: the actual
signed source packet is formatted and physically framed by one fixed
ordinary machine, without any supplied token count or expression. -/
noncomputable def momentFramedFormatterWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) (fun r=>r.packet.word)
      (fun r=>frame r.validPacket.output) MomentRequest.framedFormatterBudget :=
  wordFunction_of_finite (fun r=>r.packet.word) (fun r=>frame r.validPacket.output)
    StageRecovery.packetCallee framedMomentFormatter (fun r=>3*r.validPacket.steps+2)
    (fun r=>framedMomentFormatter_run r)

/-- `prop:time`, paper/paper.tex: the cold
source and framed exact formatter are composed with their actual
ordinary stream handoff. -/
noncomputable def MomentRequest.framedSourceBudget {B1 B2 : ℕ}
    (r : MomentRequest B1 B2) : ℕ :=
  4*r.sourceBudget+4*r.framedFormatterBudget+12

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual prepared source produces a
single framed six-field header and unchanged signed Formula word,
ready for the whole-test pool loop and exact expansion. -/
noncomputable def momentFramedSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>frame r.validPacket.output) MomentRequest.framedSourceBudget :=
  Program.WordFunction.pipe (momentSourceWordFunction B1 B2)
    (momentFramedFormatterWordFunction B1 B2)

end NearQuarticWires.StageCert.Tokens
