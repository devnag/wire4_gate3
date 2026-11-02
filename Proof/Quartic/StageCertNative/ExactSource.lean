import Proof.Quartic.StageCertNative.IndexedSourceMachine
import Proof.Quartic.StagePacketCold.Machine
import Proof.Gates.Expand.Machine

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

/-- `lem:print`, paper/paper.tex: an existing
ordinary word function is restricted to requests computed from the
actual source, without adding any encoded source fields. -/
def restrictWordFunction {A B : Type} {input output : A→List Bool} {budget : A→ℕ}
    (f : WordFunction A input output budget) (request : B→A) :
    WordFunction B (fun r=>input (request r)) (fun r=>output (request r))
      (fun r=>budget (request r)) :=
  ⟨f.program,fun r=>f.realizes (request r)⟩

/-- `lem:print`, paper/paper.tex: the six
actual exact-mode fields are the existing projection grammar; their
Formula component is correctness data erased from the input. -/
noncomputable def exactProjection {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    StagePrint.PacketInterface.ExactProjectionRequest :=
  let hint:=StageFormulaMetadata.countedHint r.packet.arity 0 (toks r.formula)
  ⟨r.index.val,hint+(r.packet.degree+r.packet.arity+10)^2,r.packet.degree,hint,
    ⟨r.packet.arity,r.formula⟩⟩

theorem exactProjection_word {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (exactProjection r).word=r.validPacket.output := by
  rw [r.formatted_exact]
  rfl

noncomputable def projectionBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  10^8*(r.validPacket.output.length+1)^2

/-- `lem:print`, paper/paper.tex: the actual
cold six-field projection preserves every original signed constant
before the exact expansion machine is called. -/
noncomputable def projectionWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) (fun r=>r.validPacket.output)
      (fun r=>frame (formulaWord ⟨r.packet.arity,r.formula⟩)) projectionBudget := by
  convert restrictWordFunction StagePacketCold.exactPacketProjection
    (fun r : MomentRequest B1 B2=>exactProjection r) using 1
  · funext r;exact (exactProjection_word r).symm
  · rfl
  · funext r
    simp only [projectionBudget,exactProjection_word]

noncomputable def exactFormulaBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*(4*indexedSourceBudget r+4*r.framedSourceBudget+12)+4*projectionBudget r+12

/-- `lem:print`, paper/paper.tex: the loop's
actual prefix-index input produces its original exact signed Formula,
through the checked source, formatter and cold projection. -/
noncomputable def exactFormulaWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) indexedMomentWord
      (fun r=>frame (formulaWord ⟨r.packet.arity,r.formula⟩)) exactFormulaBudget :=
  Program.WordFunction.pipe (indexedFormattedSourceWordFunction B1 B2)
    (projectionWordFunction B1 B2)

noncomputable def exactTerms {B1 B2 : ℕ} (r : MomentRequest B1 B2) :=
  NearCubicGates.Close.Expand.expansionMachine.expand ⟨r.packet.arity,r.formula⟩

noncomputable def exactTermsBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*exactFormulaBudget r+
    4*NearCubicGates.Close.Expand.expansionMachine.budget ⟨r.packet.arity,r.formula⟩+12

/-- `lem:print`, paper/paper.tex: the actual
published integer expansion machine is fed the complete original
signed Formula, including all failed-mask columns and tiny terms.
Its output is the literal unframed Terms codec. -/
noncomputable def exactTermsWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) indexedMomentWord
      (fun r=>termsWord (exactTerms r)) exactTermsBudget :=
  Program.WordFunction.pipe (exactFormulaWordFunction B1 B2)
    (restrictWordFunction NearCubicGates.Close.Expand.expansionMachine.wf
      (fun r : MomentRequest B1 B2=>⟨r.packet.arity,r.formula⟩))

end NearQuarticWires.StageCertNative
