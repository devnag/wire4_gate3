import Proof.Quartic.StageMainPopulation.Program
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.StageOutput.PaddedBounds
import Proof.Quartic.StageOutput.Marked
import Proof.Gates.Dispatch.Setup
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageOutput

/-- `prop:time`, paper/paper.tex: the actual
ordinary compiler includes cold initialization, both original scans,
physical source/witness addressing, output framing and final reset. -/
def populationArithmeticBudget (r : PopulationRequest) : ℕ :=
  budgetOf VV 4 r.word.length (3 * rawSteps r r.word.length + 2)

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: one actual ordinary arithmetic
machine returns the framed exact population from the literal source. -/
noncomputable def populationArithmeticMachine :
    WordFunction PopulationRequest (fun r => arithmeticInput r.word)
      PopulationRequest.output populationArithmeticBudget :=
  wordFunction_of_wmx (prog 4 (framedProgram rawProgram)) sOUT (by simp)
    (fun r => capOf 4 r.word [] (3 * rawSteps r r.word.length + 2)) (by
      intro r
      have hw := padded_width r.word.length
      obtain ⟨b, n, he, hn, ho⟩ := rawProgram_run (ctxOf 4 r.word []) r rfl (by
        change 2 * r.word.length + 8 ≤ wdOf 4 r.word.length
        omega)
      have hf := framedProgram_spec he
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by decide)
        (framedProgram rawProgram) r.word [] hf (3 * rawSteps r r.word.length + 2)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 2)
      exact ⟨τ, hrun, by simpa only [ho, PopulationRequest.output] using hout, hsh, hval⟩)

/-- `prop:time`, paper/paper.tex: framing the actual
original request and handing it to the complete arithmetic machine are
charged together, with no supplied input-format or capacity provider. -/
def populationBudget (r : PopulationRequest) : ℕ :=
  1600 * (r.word.length + 1) + 4 * populationArithmeticBudget r + 12

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: the literal original complete call,
binary offset, four binary corners and framed witness produce their
exact two-bank population by one genuine cold ordinary machine. -/
noncomputable def populationWordFunction :
    WordFunction PopulationRequest PopulationRequest.word PopulationRequest.output populationBudget := by
  let f : WordFunction PopulationRequest PopulationRequest.word
      (fun r => frame (arithmeticInput r.word)) (fun r => 400 * (r.word.length + 1)) :=
    ⟨arithmeticFraming.program, fun r => arithmeticFraming.realizes r.word⟩
  have h := Program.WordFunction.pipe f populationArithmeticMachine
  convert h using 1
  funext r
  simp [populationBudget]
  ring

end NearQuarticWires.StageMainPopulation
