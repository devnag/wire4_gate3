import Proof.Quartic.StageCarrierEnvelope.Body

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: one
fixed ordinary controller performs its actual metadata call once,
then emits the immutable retained-source envelope. -/
noncomputable def envelopeProgram (B1 B2 : ℕ) :
    WMX ((metadataWordFunction B1 B2).program.tapeCount+3) 16 :=
  .seq (metadataBank B1 B2) (.wm (envelopeBody B1 B2))

noncomputable def envelopeSteps {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  2*metadataBudget r+200*((StagePrint.TermsCarrier.word r).length+1)+1+bodySteps r

/-- `prop:time`, paper/paper.tex: this
SAME actual ordinary clock includes the once-only metadata call,
all source copies and the final ordinary compilation and head reset. -/
noncomputable def envelopeBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  2*envelopeSteps r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: the sole literal compiled carrier is sufficient for
the complete physical envelope, with no supplied source or metadata. -/
theorem envelopeProgram_run {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ∃ b, WXExec (envelopeCapacity r) (envelopeProgram B1 B2)
      (idealStart ((metadataWordFunction B1 B2).program.tapeCount+3) 16
        (StagePrint.TermsCarrier.word r) (bankLens (metadataWordFunction B1 B2).program.tapeCount (metadataBudget r)))
      b (envelopeSteps r) ∧
      b.st (bankOut (metadataWordFunction B1 B2).program.tapeCount)=frame (StagePrint.CarrierEnvelope.word r) := by
  obtain ⟨a,ea,ha⟩:=metadataBank_run r (envelopeCapacity r) (by
    have hp : 0≤2^(natBitLength (StageLift.preparedWordOf r).length+1):=Nat.zero_le _
    change 4*(StagePrint.TermsCarrier.word r).length+4≤
      100*((StagePrint.TermsCarrier.word r).length+2^(natBitLength (StageLift.preparedWordOf r).length+1)+r.child.call.n+10)
    omega)
  obtain ⟨b,eb,hb⟩:=envelopeBody_run r a ha
  exact ⟨b,(WXExec.seq ea (WXExec.wm eb)).mono (by unfold envelopeSteps;omega),hb⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual cold ordinary producer begins with only
TermsCarrier.word and returns the fixed eleven-field envelope at
its unchanged literal output codec and SAME complete physical budget. -/
noncomputable def carrierEnvelopeProducer (B1 B2 : ℕ) : StagePrint.CarrierEnvelope.Producer B1 B2 :=
  ⟨envelopeBudget,wordFunction_of_ideal (envelopeProgram B1 B2)
    (bankOut (metadataWordFunction B1 B2).program.tapeCount) (by simp [bankOut])
    envelopeCapacity (fun r=>bankLens (metadataWordFunction B1 B2).program.tapeCount (metadataBudget r))
    envelopeSteps (fun _=>le_rfl) (by
      intro r
      exact ⟨by simp [bankLens,bankOut],envelopeProgram_run r⟩)⟩

end NearQuarticWires.StageCarrierEnvelope
