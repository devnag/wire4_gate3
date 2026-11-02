import Proof.Quartic.StageCertTests.PrepScheduleCost
import Proof.Quartic.StageRecovery.OutputFrame

/-!
# The actual scheduler with a physically framed output

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests

/-- `prop:time`, paper/paper.tex: the
scheduler's output markers and final delimiter are written by real
instructions, included in its complete cold compiled budget. -/
noncomputable def framedScheduleBudget {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  langBudget StageRecovery.packetCallee (prepScheduleSizes B1 B2) VV MM r.word
    (3*prepScheduleSteps r.call r.selected.1+2)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the actual cold scheduler prints the exact
framed metadata stream, so it can be consumed and erased through an
ordinary physical call without a fixed-length output oracle. -/
noncomputable def framedScheduleWordFunction (B1 B2 : ℕ) :
    WordFunction (PreparedScheduleRequest B1 B2) PreparedScheduleRequest.word
      (fun r => frame r.output) framedScheduleBudget :=
  wordFunction_of_lang PreparedScheduleRequest.word (fun r => frame r.output)
    StageRecovery.packetCallee (prepScheduleSizes B1 B2)
    (StageRecovery.OutputFrame.framedProgram prepScheduleProgram)
    (fun r => 3*prepScheduleSteps r.call r.selected.1+2)
    (by
      intro r
      have hw := r.widths
      obtain ⟨b,n,he,hn,ho⟩ := prepScheduleProgram_spec
        (ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2) r.word) r.call r.selected.1
        (frame (Program.witnessPrefix r.call r.selected.1 r.witness)) r.word_eq hw.1 hw.2
      have hf := StageRecovery.OutputFrame.framedProgram_spec he
      have hmark : StageRecovery.OutputFrame.markedState (a0 : DS VV MM)=a0 := rfl
      rw [hmark] at hf
      refine ⟨StageRecovery.OutputFrame.framedState b,3*n+2,hf,?_,by omega⟩
      change frame b.out=frame r.output
      rw [ho]
      rfl)
    (by
      intro r
      have h := r.widths.1
      change 1≤(ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2) r.word).Wd
      omega)

/-- `prop:time`, paper/paper.tex: physical
metadata framing preserves a polynomial original-call budget, including
all cold setup, output writes, and final tape-head returns. -/
theorem framedScheduleBudget_polynomial (B1 B2 : ℕ) :
    PreparedPolynomial (B1 := B1) (B2 := B2) framedScheduleBudget := by
  have hN := ((PreparedPolynomial.const 3).mul
    (PreparedPolynomial.sourceSteps (B1 := B1) (B2 := B2))).add (PreparedPolynomial.const 2)
  have hG := PreparedPolynomial.compilationScale (B1 := B1) (B2 := B2)
  have hI := PreparedPolynomial.inputLength (B1 := B1) (B2 := B2)
  have hu := ((PreparedPolynomial.const (10^6)).mul
    ((hN.add (PreparedPolynomial.const 1)).mul (hG.pow 2))).add
      ((PreparedPolynomial.const 10).mul hI)
  refine hu.mono ?_
  intro r
  exact NearCubicGates.Close.CellsPack.lang_le2 StageRecovery.packetCallee (prepScheduleSizes B1 B2)
    r.word (3*prepScheduleSteps r.call r.selected.1+2)

end NearQuarticWires.StageCertificateControl
