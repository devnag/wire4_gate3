import Proof.Quartic.StageOutput.OutputProgram

/-!
# A uniform ordinary word function for Step 5

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The ordinary program first performs the charged padding
pass, then initializes its binary arithmetic workspace from that padded
word, computes the endpoints, and writes the exact canonical output.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

abbrev ValidRequest := {r : OutputRequest // r.Admissible}

def arithmeticRunBudget (r : OutputRequest) : ℕ :=
  budgetOf VV 4 r.padded.length (outputSteps (wdOf 4 r.padded.length))

noncomputable def arithmeticMachine :
    WordFunction ValidRequest (fun r => arithmeticInput r.1.padded)
      (fun r => outputWord r.1.result) (fun r => arithmeticRunBudget r.1) :=
  wordFunction_of_wmx (prog 4 outputProgram) sOUT (by simp)
    (fun r => capOf 4 r.1.padded [] (outputSteps (wdOf 4 r.1.padded.length))) (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := outputProgram_spec (C := ctxOf 4 r.1.padded []) r.1 r.2 rfl
        (padded_width _) (padded_word_capacity _)
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by norm_num) outputProgram r.1.padded [] he
        (outputSteps (wdOf 4 r.1.padded.length)) hn
      exact ⟨τ, hrun, by simpa only [ho] using hout, hsh, hval⟩)

def paddedOutputBudget (r : OutputRequest) : ℕ :=
  1600 * (r.padded.length + 1) + 4 * arithmeticRunBudget r + 12

noncomputable def paddedOutputMachine :
    WordFunction ValidRequest (fun r => r.1.padded) (fun r => outputWord r.1.result)
      (fun r => paddedOutputBudget r.1) := by
  let f : WordFunction ValidRequest (fun r => r.1.padded)
      (fun r => frame (arithmeticInput r.1.padded)) (fun r => 400 * (r.1.padded.length + 1)) :=
    ⟨arithmeticFraming.program, fun r => arithmeticFraming.realizes r.1.padded⟩
  have h := Program.WordFunction.pipe f arithmeticMachine
  convert h using 1
  funext r
  simp [paddedOutputBudget]
  ring

def rawOutputBudget (r : OutputRequest) : ℕ :=
  4 * prepareBudget r + 4 * paddedOutputBudget r + 12

noncomputable def rawOutputMachine :
    WordFunction ValidRequest (fun r => r.1.word) (fun r => outputWord r.1.result)
      (fun r => rawOutputBudget r.1) := by
  let f : WordFunction ValidRequest (fun r => r.1.word) (fun r => frame r.1.padded)
      (fun r => prepareBudget r.1) :=
    ⟨prepareMachine.program, fun r => prepareMachine.realizes r.1⟩
  exact Program.WordFunction.pipe f paddedOutputMachine

noncomputable def outputBudget (B1 B2 : ℕ) (c : Call) (w : List Bool) : ℕ :=
  rawOutputBudget (outputRequest B1 B2 c w)

/-- The exact `output` field of the counter's ordinary machine components. -/
noncomputable def output (B1 B2 : ℕ) :
    WordFunction (Call × List Bool) (fun r => Program.mainWord B1 B2 r.1 r.2)
      (fun r => outputWord (Program.admittedValue B1 B2 Builder.value r.1 r.2))
      (fun r => outputBudget B1 B2 r.1 r.2) where
  program := rawOutputMachine.program
  realizes r := by
    have h := rawOutputMachine.realizes ⟨outputRequest B1 B2 r.1 r.2, outputRequest_admissible B1 B2 r.1 r.2⟩
    simpa only [outputRequest_word, outputRequest_result, outputBudget] using h

end NearQuarticWires.StageOutput
