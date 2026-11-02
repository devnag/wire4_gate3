import Proof.Quartic.StageMainMask.StructuralProgram
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.StageOutput.PaddedBounds
import Proof.Quartic.StageOutput.Marked
import Proof.Gates.Dispatch.Setup
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageOutput

/-- `prop:time`, paper/paper.tex: the actual
ordinary compiler pays initialization, the framed structural program,
all source scans and final head rewinding. -/
def structuralArithmeticBudget (r : StructuralRawRequest) : ℕ :=
  budgetOf VV 4 r.word.length (3 * structuralRawSteps r r.word.length + 2)

/-- `def:mask` and `prop:time`, paper/paper.tex: the actual binary arithmetic input initializes and
executes one uniform structural-mask machine with a framed bit reply. -/
noncomputable def structuralArithmeticMachine :
    WordFunction StructuralRawRequest (fun r => arithmeticInput r.word)
      (fun r => frame [r.bit]) structuralArithmeticBudget :=
  wordFunction_of_wmx (prog 4 (framedProgram structuralRawProgram)) sOUT (by simp)
    (fun r => capOf 4 r.word [] (3 * structuralRawSteps r r.word.length + 2)) (by
      intro r
      have hw := padded_width r.word.length
      obtain ⟨b, n, he, hn, ho⟩ := structuralRawProgram_spec (C := ctxOf 4 r.word []) r rfl (by
        change 2 * r.word.length + 8 ≤ wdOf 4 r.word.length
        omega)
      have hf := framedProgram_spec he
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by decide)
        (framedProgram structuralRawProgram) r.word [] hf
        (3 * structuralRawSteps r r.word.length + 2)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 2)
      exact ⟨τ, hrun, by simpa only [ho] using hout, hsh, hval⟩)

/-- `prop:time`, paper/paper.tex: ordinary source
framing and the complete structural arithmetic machine are charged
together, including the actual three-bit framed reply. -/
def structuralRawBudget (r : StructuralRawRequest) : ℕ :=
  1600 * (r.word.length + 1) + 4 * structuralArithmeticBudget r + 12

/-- `def:mask` and `prop:time`, paper/paper.tex: the literal original call and five scalar fields
produce their exact framed structural bit by a cold ordinary machine,
without supplied initialized registers or an original incidence table. -/
noncomputable def structuralRawMachine :
    WordFunction StructuralRawRequest StructuralRawRequest.word
      (fun r => frame [r.bit]) structuralRawBudget := by
  let f : WordFunction StructuralRawRequest StructuralRawRequest.word
      (fun r => frame (arithmeticInput r.word))
      (fun r => 400 * (r.word.length + 1)) :=
    ⟨arithmeticFraming.program, fun r => arithmeticFraming.realizes r.word⟩
  have h := Program.WordFunction.pipe f structuralArithmeticMachine
  convert h using 1
  funext r
  simp [structuralRawBudget]
  ring

end NearQuarticWires.StageMainMask
