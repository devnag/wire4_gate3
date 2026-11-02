import Proof.Quartic.StagePrintContext.Body
import Proof.Quartic.StagePrintContext.Capacity

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests StageFormulaMetadata StageRecovery.OutputFrame

/-- `lem:print`, paper/paper.tex: the actual
preparation is acquired before one completely framed common context
is emitted for either later walk consumer. -/
def contextProgram : St VV MM := .seq acquireContext (framedProgram contextBody)

/-- `prop:time`, paper/paper.tex: the complete
source clock includes acquisition, all common fields, the outer frame
and the final sequencing step. -/
noncomputable def contextSteps {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  readSteps r+3*bodySteps r (finiteWidth r.word.length)+3

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal preparation alone produces the exact
framed common context, without Gamma, walk data, a decoded source
or any assumed downstream supplier. -/
theorem contextProgram_run {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) :
    Hs (finiteContext StageRecovery.packetCallee r.word) contextProgram (a0 : DS VV MM)
      (contextSteps r) (fun last=>last.out=frame (StagePrint.Context.word r)) := by
  let C:=finiteContext StageRecovery.packetCallee r.word
  have capacity:=context_capacity r
  have hMin : 5≤C.Wd := by dsimp [C,finiteContext,finiteWidth];omega
  unfold contextProgram
  refine (Hs.seq (t2:=3*bodySteps r C.Wd+2)
    (acquireContext_run C r rfl capacity.1) ?_).mono
      (by unfold contextSteps;change _≤readSteps r+3*bodySteps r C.Wd+3;omega) (fun _ h=>h)
  rintro a ⟨hd,ho,hc,hv⟩
  have hsource:=StagePrint.Header.HeaderSourceData.of_compact (StagePrint.Context.header r) hd
  have er:=contextBody_run C r a hc hv hsource hd.callBytes hMin capacity.2.1 capacity.2.2
  obtain ⟨b,n,he,hn,hout⟩:=er
  have hframe:=framedProgram_spec he
  have hmark : markedState a=a := by
    unfold markedState markedBits
    simp only [ho,List.flatMap_nil]
    rw [←ho]
  rw [hmark] at hframe
  refine ⟨framedState b,3*n+2,hframe,by omega,?_⟩
  change frame b.out=frame (StagePrint.Context.word r)
  rw [hout,ho,List.nil_append]

/-- `prop:time`, paper/paper.tex: the complete
ordinary clock includes measured finite allocation, binary compilation,
output movement and restoration of all memory and stream heads. -/
noncomputable def contextBudget {B1 B2 : ℕ} (r : PreparedScheduleRequest B1 B2) : ℕ :=
  finiteBudget StageRecovery.packetCallee VV MM r.word (contextSteps r)

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed ordinary source machine supplies the
unchanged eleven-field context to both exact and modular consumers. -/
noncomputable def contextProducer (B1 B2 : ℕ) : StagePrint.Context.Producer B1 B2 :=
  ⟨contextBudget,wordFunction_of_finite PreparedScheduleRequest.word
    (fun r=>frame (StagePrint.Context.word r)) StageRecovery.packetCallee contextProgram contextSteps
    (by
      intro r
      obtain ⟨last,n,he,hn,hout⟩:=contextProgram_run r
      exact ⟨last,n,he,hout,hn⟩)⟩

end NearQuarticWires.StagePrintContext
