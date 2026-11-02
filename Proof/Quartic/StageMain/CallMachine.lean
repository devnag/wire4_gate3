import Proof.Quartic.StageMain.CallProgram
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.StageOutput.PaddedBounds
import Proof.Quartic.Program.Pipe

/-!
# An ordinary word function for literal call predicates

Paper: `def:class`, paper/paper.tex, Step 4 of
`sec:algorithm`, and `prop:time`.
The binary program reads both the packed point and the call from its
input tape. A paid linear framing pass supplies the arithmetic machine;
the budget includes framing, binary workspace initialization, evaluation,
and output. No gate values are supplied separately.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageOutput

def predicateArithmeticBudget (L : ℕ) : ℕ := budgetOf VV 4 L (predicateSteps L)

def predicateBudget (L : ℕ) : ℕ := 1600 * (L + 1) + 4 * predicateArithmeticBudget L + 12

noncomputable def predicateArithmeticMachine :
    WordFunction PredicateRequest (fun r => arithmeticInput r.word) (fun r => [r.value])
      (fun r => predicateArithmeticBudget r.word.length) :=
  wordFunction_of_wmx (prog 4 predicateProgram) sOUT (by simp)
    (fun r => capOf 4 r.word [] (predicateSteps r.word.length)) (by
      intro r
      have hw := padded_width r.word.length
      obtain ⟨b, n, he, hn, ho⟩ := predicateProgram_spec (C := ctxOf 4 r.word []) r rfl (by
        change r.word.length + 4 ≤ wdOf 4 r.word.length
        omega)
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by decide) predicateProgram r.word [] he _ hn
      exact ⟨τ, hrun, by simpa only [ho] using hout, hsh, hval⟩)

/-- The raw point-and-call word is evaluated by one uniform ordinary program. -/
noncomputable def predicateMachine :
    WordFunction PredicateRequest PredicateRequest.word (fun r => [r.value])
      (fun r => predicateBudget r.word.length) := by
  let f : WordFunction PredicateRequest PredicateRequest.word (fun r => frame (arithmeticInput r.word))
      (fun r => 400 * (r.word.length + 1)) :=
    ⟨arithmeticFraming.program, fun r => arithmeticFraming.realizes r.word⟩
  have h := Program.WordFunction.pipe f predicateArithmeticMachine
  convert h using 1
  funext r
  simp [predicateBudget]
  ring

end NearQuarticWires.StageMain
