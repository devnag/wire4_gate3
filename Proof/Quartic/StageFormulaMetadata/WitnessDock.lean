import Proof.Quartic.StageFormulaMetadata.Machine
import Proof.Foundations.OrdinaryMachine

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageRecovery (packetCallee tokenStream)

/-- `lem:print`, paper/paper.tex: two successful
executions of the same actual machine on the same literal input
have identical output bytes, independent of their clock bounds. -/
theorem sameProgram_output (program : RepairOrdinary.Program) (input : List Bool)
    (first second : ℕ) (left right : List Bool)
    (hl : ∃ receipt,run program.machine first (program.inputTapes input)=some receipt ∧
      receipt.final.tapes program.outputTape=left)
    (hr : ∃ receipt,run program.machine second (program.inputTapes input)=some receipt ∧
      receipt.final.tapes program.outputTape=right) : left=right := by
  obtain ⟨r,hrun,hout⟩:=hl
  obtain ⟨s,hsrun,hsout⟩:=hr
  have h1:=run_moreFuel program.machine first second (program.inputTapes input) r hrun
  have h2:=run_moreFuel program.machine second first (program.inputTapes input) s hsrun
  rw [Nat.add_comm second first] at h2
  have heq : r=s := Option.some.inj (h1.symm.trans h2)
  subst s
  exact hout.symm.trans hsout

/-- `lem:print`, paper/paper.tex: each actual
source emitter may use its own proved Formula witness. The erased
validity choice cannot change a byte of the formatter's output. -/
theorem ValidPacket.output_of_source (request : ValidPacket) (formula : Formula request.val.arity)
    (hsource : request.val.payload=tokenStream (toks formula)) :
    request.output=formattedWord request.val.index request.val.degree request.val.arity
      request.val.modulus (toks formula) := by
  let output:=formattedWord request.val.index request.val.degree request.val.arity
    request.val.modulus (toks formula)
  let steps:=formatterSteps request.val (toks formula) (finiteWidth request.val.word.length)
  let sameMachine:=wordFunction_of_finite (fun _ : Unit=>request.val.word)
    (fun _ : Unit=>output) packetCallee formatterProgram (fun _ : Unit=>steps) (by
      intro _
      obtain ⟨b,n,he,hn,ho⟩:=formatterProgram_spec
        (finiteContext packetCallee request.val.word) request.val (toks formula) hsource request.mode rfl le_rfl
      exact ⟨b,n,he,ho,hn⟩)
  have hp : sameMachine.program=rawFormatterWordFunction.program := rfl
  have hs:=sameMachine.realizes ()
  rw [hp] at hs
  exact sameProgram_output rawFormatterWordFunction.program request.val.word request.budget
    (finiteBudget packetCallee VV MM request.val.word steps) request.output output
    (rawFormatterWordFunction.realizes request) hs

end NearQuarticWires.StageFormulaMetadata
