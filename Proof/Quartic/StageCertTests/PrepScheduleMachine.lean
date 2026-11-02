import Proof.Quartic.StageCertTests.PrepScheduleSource
import Proof.Quartic.StageCertTests.PrepScheduleWidth

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:algorithm`, paper/paper.tex:
the true branch of the original preparation stage has the literal
selected public parameters certified by its own dispatch. -/
structure PreparedScheduleRequest (B1 B2 : ℕ) where
  call : Call
  witness : List Bool
  selected : Program.Selected call
  dispatched : Program.dispatch B1 B2 call = some selected

/-- `sec:algorithm`, paper/paper.tex:
the direct scheduler consumes the original actual preparation word. -/
noncomputable def PreparedScheduleRequest.word {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : List Bool :=
  Program.prepWord B1 B2 r.call r.witness

/-- `sec:algorithm`, paper/paper.tex:
the output is the exact complete whole-test request sequence. -/
noncomputable def PreparedScheduleRequest.output {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : List Bool :=
  (certificateMetadata r.selected.1 r.call.kind).flatMap TestMetadata.word

/-- `sec:algorithm`, paper/paper.tex:
the actual preparation input has no additional scheduling header,
decoded metadata, bitmap or precomputed moment table. -/
theorem PreparedScheduleRequest.word_eq {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    r.word = true :: (callWord r.call ++ Program.parametersWord r.selected.1 ++
      frame (Program.witnessPrefix r.call r.selected.1 r.witness)) := by
  unfold PreparedScheduleRequest.word Program.prepWord Program.stageWord
  rw [r.dispatched]

/-- `prop:time`, paper/paper.tex:
the direct original-source context obtains every required width
from its literal arity header, using only proved dispatch bounds. -/
theorem PreparedScheduleRequest.widths {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    let C := ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2) r.word
    (callWord r.call).length+2 ≤ C.Wd ∧ 64*(scheduleHint r.selected.1+1) ≤ C.Wd := by
  have h := prepSchedule_context_widths r.dispatched
    (Program.parametersWord r.selected.1 ++ frame (Program.witnessPrefix r.call r.selected.1 r.witness))
  simpa only [r.word_eq,List.append_assoc] using h

/-- `prop:time`, paper/paper.tex:
the actual direct-source schedule budget includes cold setup,
complete preparation input copying, all parsing and nested test generation. -/
noncomputable def PreparedScheduleRequest.budget {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  langBudget StageRecovery.packetCallee (prepScheduleSizes B1 B2) VV MM r.word
    (prepScheduleSteps r.call r.selected.1)

/-- `sec:params` and `sec:algorithm`, paper/paper.tex: an actual cold word machine derives
the entire exact test schedule directly from the original preparation
source, with no extra header or assumed decoded supplier. -/
noncomputable def prepScheduleWordFunction (B1 B2 : ℕ) :
    WordFunction (PreparedScheduleRequest B1 B2) PreparedScheduleRequest.word
      PreparedScheduleRequest.output PreparedScheduleRequest.budget :=
  wordFunction_of_lang PreparedScheduleRequest.word PreparedScheduleRequest.output
    StageRecovery.packetCallee (prepScheduleSizes B1 B2) prepScheduleProgram
    (fun r => prepScheduleSteps r.call r.selected.1) (by
      intro r
      have hw := r.widths
      obtain ⟨b,n,he,hn,ho⟩ := prepScheduleProgram_spec
        (ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2) r.word) r.call r.selected.1
        (frame (Program.witnessPrefix r.call r.selected.1 r.witness)) r.word_eq hw.1 hw.2
      exact ⟨b,n,he,ho,hn⟩) (by
      intro r
      have h := r.widths.1
      change 1 ≤ (ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2) r.word).Wd
      omega)

end NearQuarticWires.StageCertTests
