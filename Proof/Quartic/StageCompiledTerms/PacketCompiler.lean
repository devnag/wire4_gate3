import Proof.Quartic.StageCompiledTerms.FramedFormatter
import Proof.Quartic.StagePacketCold.Machine
import Proof.Quartic.StagePrint.TermsCarrierTarget

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the proof
index names an original walk; its runtime input is only the actual
five-field raw packet emitted by the complete source machine. -/
abbrev WalkRequest (B1 B2 : ℕ) :=
  (r : Greedy.PrintRequest B1 B2) × Fin (r.child.cellCall.seed.N^8)

/-- `lem:print`, paper/paper.tex: the finite
family request is the literal normalized formatter output. -/
noncomputable def walkFamily {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    StageRecovery.FamilyCompileRequest :=
  StageFormulaMetadata.modularFamily (w.1.prime^w.1.child.selected.1.e)
    (StageLift.residueDegreeBound w.1.child.selected.1 w.1.prime)
    (StageLift.sourceWalkFormula w.1 w.2) (Reconstruct.PrintRequest.two_le_modulus w.1)
    (StageLift.sourceWalkFormula_degree w.1 w.2)

/-- `lem:print`, paper/paper.tex: the original
encoded index precedes the physically counted family request. -/
noncomputable def indexedWalkFamily {B1 B2 : ℕ} (w : WalkRequest B1 B2) :
    StagePrint.Downstream.IndexedFamilyPacket := ⟨w.2.val,walkFamily w⟩

/-- `prop:time`, paper/paper.tex: each actual
packet charges formatter, encoded-index projection, modular recovery
and both ordinary framed handoffs exactly once. -/
noncomputable def packetCompilerBudget {B1 B2 : ℕ} (w : WalkRequest B1 B2) : ℕ :=
  4*(4*framedFormatterBudget (StageLift.validSourceWalkPacket w.1 w.2)+
    4*(10^8*((indexedWalkFamily w).word.length+1)^2)+12)+
    4*(walkFamily w).modularTermsBudget+12

/-- `lem:print`, paper/paper.tex: one fixed
ordinary machine compiles the actual raw source packet into canonical
framed modular Terms. Every source and compiler adapter is executed;
no separated Formula, coefficient table or compiler result is supplied. -/
noncomputable def packetCompilerWordFunction (B1 B2 : ℕ) :
    WordFunction (WalkRequest B1 B2)
      (fun w=>(StageLift.sourceWalkPacket w.1 w.2).word)
      (fun w=>frame (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2)))
      packetCompilerBudget := by
  let f : WordFunction (WalkRequest B1 B2)
      (fun w=>(StageLift.sourceWalkPacket w.1 w.2).word)
      (fun w=>frame (indexedWalkFamily w).word)
      (fun w=>framedFormatterBudget (StageLift.validSourceWalkPacket w.1 w.2)) :=
    ⟨framedFormatterWordFunction.program,fun w=>by
      have hr:=framedFormatterWordFunction.realizes (StageLift.validSourceWalkPacket w.1 w.2)
      rw [StageLift.sourceWalkPacket_formatter_output] at hr
      exact hr⟩
  let g : WordFunction (WalkRequest B1 B2) (fun w=>(indexedWalkFamily w).word)
      (fun w=>frame (walkFamily w).word)
      (fun w=>10^8*((indexedWalkFamily w).word.length+1)^2) :=
    ⟨StagePacketCold.modularPacketProjection.program,fun w=>
      StagePacketCold.modularPacketProjection.realizes (indexedWalkFamily w)⟩
  let h : WordFunction (WalkRequest B1 B2) (fun w=>(walkFamily w).word)
      (fun w=>frame (termsWord (StagePrint.TermsCarrier.actualTerms w.1 w.2)))
      (fun w=>(walkFamily w).modularTermsBudget) :=
    ⟨StageRecovery.modularTermsWordFunction.program,fun w=>
      StageRecovery.modularTermsWordFunction.realizes (walkFamily w)⟩
  exact Program.WordFunction.pipe (Program.WordFunction.pipe f g) h

end NearQuarticWires.StageCompiledTerms
