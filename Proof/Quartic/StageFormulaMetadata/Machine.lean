import Proof.Quartic.StageFormulaMetadata.Program
import Proof.Quartic.StageFormulaMetadata.FiniteMachine

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageRecovery (tokenStream packetCallee)

/-- `lem:print`, paper/paper.tex: the semantic
formula is selected only from the erased proof of the actual source
codec, without adding any formula field to the runtime packet. -/
noncomputable def ValidPacket.formula (request : ValidPacket) : Formula request.val.arity :=
  Classical.choose request.property

/-- `lem:print`, paper/paper.tex: the actual
producer's erased validity proves the literal emitted token bytes. -/
theorem ValidPacket.source (request : ValidPacket) :
    request.val.payload=tokenStream (toks request.formula) :=
  (Classical.choose_spec request.property).1

/-- `lem:print`, paper/paper.tex: the original
degree bound is source validity, not a decoded runtime oracle. -/
theorem ValidPacket.degree (request : ValidPacket) : request.formula.degree≤request.val.degree :=
  (Classical.choose_spec request.property).2.1

/-- `lem:print`, paper/paper.tex: actual sources
use exactly the signed-exact or positive modular formatting mode. -/
theorem ValidPacket.mode (request : ValidPacket) : request.val.modulus=0 ∨ 2 ≤ request.val.modulus :=
  (Classical.choose_spec request.property).2.2

/-- `lem:print`, paper/paper.tex: the mathematical
output specification is the unchanged indexed compiler request. -/
noncomputable def ValidPacket.output (request : ValidPacket) : List Bool :=
  formattedWord request.val.index request.val.degree request.val.arity request.val.modulus (toks request.formula)

/-- `prop:time`, paper/paper.tex: actual token
scans determine the complete source-program clock of this raw input. -/
noncomputable def ValidPacket.steps (request : ValidPacket) : ℕ :=
  formatterSteps request.val (toks request.formula) (finiteWidth request.val.word.length)

/-- `prop:time`, paper/paper.tex: the final
physical ledger includes the actual measured allocator, compilation,
source/output/store returns and both postfix passes. -/
noncomputable def ValidPacket.budget (request : ValidPacket) : ℕ :=
  finiteBudget packetCallee VV MM request.val.word request.steps

/-- `lem:print` and `prop:time`, paper/paper.tex: the cold raw-postfix formatter is one fixed ordinary
multitape word function, with no supplied count, syntax size, byte
length, workspace hint, decoded Formula or coefficient expansion. -/
noncomputable def rawFormatterWordFunction :
    WordFunction ValidPacket (fun request=>request.val.word) ValidPacket.output ValidPacket.budget :=
  wordFunction_of_finite (fun request=>request.val.word) ValidPacket.output packetCallee formatterProgram
    ValidPacket.steps (by
      intro request
      obtain ⟨b,n,he,hn,hout⟩:=formatterProgram_spec
        (finiteContext packetCallee request.val.word) request.val (toks request.formula)
        request.source request.mode rfl le_rfl
      exact ⟨b,n,he,hout,hn⟩)

end NearQuarticWires.StageFormulaMetadata
