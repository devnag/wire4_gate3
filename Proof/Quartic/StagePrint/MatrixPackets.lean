import Proof.MachineModel.OrdinaryMatrixScheduler
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: the signed Boolean-product packets of an actual separated-cut request. -/
noncomputable def packetBudget (a : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) : ℕ :=
  MatrixPacketSchedulerBounds.envelope a r

/-- `lem:print`, paper/paper.tex: one finite machine prints every signed bit plane from the encoded cuts and center-coordinate columns. -/
noncomputable def packetPrinter (a : WilliamsAlgorithm) :
    WordFunction MatrixScoreBatch.Request MatrixScoreBatch.word MatrixScoreBatch.output (packetBudget a) where
  program := MatrixPacketScheduler.program a (MatrixPacketSchedulerBounds.E a) (MatrixPacketSchedulerBounds.C a)
  realizes r := by
    obtain ⟨actual, hr, ho, _, _, _, _⟩ := MatrixPacketScheduler.scheduler_run a r
    exact ⟨actual, hr, ho⟩

/-- `lem:print`, paper/paper.tex: the packet machine has a quadratic table bound with a fixed polynomial in the encoded widths. -/
theorem packetBudget_eq (a : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) :
    packetBudget a r = MatrixPacketSchedulerBounds.coefficient a * (r.U + 1) ^ 2 *
      (r.d + r.p + 1) ^ MatrixPacketSchedulerBounds.exponent a := rfl

/-- `lem:print`, paper/paper.tex: all packet heads return to zero at the same physical budget. -/
theorem packetPrinter_heads (a : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) :
    ∃ actual, run (packetPrinter a).program.machine (packetBudget a r)
      ((packetPrinter a).program.inputTapes (MatrixScoreBatch.word r)) = some actual ∧
      actual.final.tapes (packetPrinter a).program.outputTape = MatrixScoreBatch.output r ∧
      ∀ i, actual.final.heads i = 0 := by
  obtain ⟨actual, hr, ho, _, hh, _, _⟩ := MatrixPacketScheduler.scheduler_run a r
  exact ⟨actual, hr, ho, hh⟩

end NearQuarticWires.StagePrint
