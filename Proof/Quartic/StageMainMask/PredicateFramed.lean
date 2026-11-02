import Proof.Quartic.StageMain.CallMachine
import Proof.Quartic.StageOutput.Marked
import Proof.Gates.Dispatch.Main

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMain StageOutput

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the actual predicate evaluator pays
binary workspace initialization and every framed output bit. -/
def framedPredicateArithmeticBudget (L : ℕ) : ℕ :=
  budgetOf VV 4 L (3 * predicateSteps L + 2)

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
one complete original call is evaluated at the actual packed point,
with a framed singleton Boolean reply for the ordinary call selector. -/
noncomputable def framedPredicateArithmeticMachine :
    WordFunction PredicateRequest (fun r => arithmeticInput r.word)
      (fun r => frame [r.value]) (fun r => framedPredicateArithmeticBudget r.word.length) :=
  wordFunction_of_wmx (prog 4 (framedProgram predicateProgram)) sOUT (by simp)
    (fun r => capOf 4 r.word [] (3 * predicateSteps r.word.length + 2)) (by
      intro r
      have hw := padded_width r.word.length
      obtain ⟨b, n, he, hn, ho⟩ := predicateProgram_spec (C := ctxOf 4 r.word []) r rfl (by
        change r.word.length + 4 ≤ wdOf 4 r.word.length
        omega)
      have hf := framedProgram_spec he
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by decide)
        (framedProgram predicateProgram) r.word [] hf
        (3 * predicateSteps r.word.length + 2)
        (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 2)
      exact ⟨τ, hrun, by simpa only [ho] using hout, hsh, hval⟩)

/-- `prop:time`, paper/paper.tex: the complete
predicate subroutine includes actual source framing and its charged
ordinary composition with the framed arithmetic evaluator. -/
def framedPredicateBudget (L : ℕ) : ℕ :=
  1600 * (L + 1) + 4 * framedPredicateArithmeticBudget L + 12

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the literal packed point followed by the complete original call is
read from the source of one cold ordinary predicate machine. -/
noncomputable def framedPredicateMachine :
    WordFunction PredicateRequest PredicateRequest.word (fun r => frame [r.value])
      (fun r => framedPredicateBudget r.word.length) := by
  let f : WordFunction PredicateRequest PredicateRequest.word
      (fun r => frame (arithmeticInput r.word))
      (fun r => 400 * (r.word.length + 1)) :=
    ⟨arithmeticFraming.program, fun r => arithmeticFraming.realizes r.word⟩
  have h := Program.WordFunction.pipe f framedPredicateArithmeticMachine
  convert h using 1
  funext r
  simp [framedPredicateBudget]
  ring

/-- `prop:time`, paper/paper.tex: the actual
framed original-predicate subroutine has polynomial source-word cost. -/
theorem framedPredicateBudget_polynomial : PolyB framedPredicateBudget := by
  unfold framedPredicateBudget framedPredicateArithmeticBudget predicateSteps budgetOf setupCost KC wdOf
  polyb

end NearQuarticWires.StageMainMask
