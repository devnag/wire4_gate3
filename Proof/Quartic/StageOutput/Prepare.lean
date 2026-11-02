import Proof.Quartic.StageOutput.PaddingDispatch

/-!
# Ordinary preparation for Step 5 arithmetic

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. One uniform ordinary program copies the tagged scalar
request, explicitly writes its arithmetic padding, and frames the result.
The already encoded answer branch is copied without padding.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def paddingRunBudget (r : OutputRequest) : ℕ :=
  budgetOf VV 4 r.word.length (3 * paddingSteps r (wdOf 4 r.word.length) + 2)

/-- The framed arithmetic-input version of the padding program. -/
noncomputable def paddingArithmeticMachine :
    WordFunction OutputRequest (fun r => arithmeticInput r.word) (fun r => frame r.padded) paddingRunBudget :=
  wordFunction_of_wmx (prog 4 (framedProgram paddingProgram)) sOUT (by simp)
    (fun r => capOf 4 r.word [] (3 * paddingSteps r (wdOf 4 r.word.length) + 2)) (by
      intro r
      have hW : r.word.length + 2 ≤ (ctxOf 4 r.word []).Wd := by
        change r.word.length + 2 ≤ (r.word.length + 4) ^ 4
        exact (by omega : r.word.length + 2 ≤ r.word.length + 4).trans
          (Nat.le_self_pow (by norm_num) _)
      have hL : r.word.length + 2 < 2 ^ (ctxOf 4 r.word []).Wd :=
        lt_of_le_of_lt hW Nat.lt_two_pow_self
      obtain ⟨b, n, he, hn, ho⟩ := paddingProgram_spec (C := ctxOf 4 r.word []) r rfl hW hL
      have hf := framedProgram_spec he
      obtain ⟨τ, hrun, hout, hsh, hval⟩ := prog_spec 4 (by norm_num)
        (framedProgram paddingProgram) r.word [] hf
        (3 * paddingSteps r (wdOf 4 r.word.length) + 2) (by exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 2)
      exact ⟨τ, hrun, by simpa only [ho] using hout, hsh, hval⟩)

def prepareBudget (r : OutputRequest) : ℕ := 1600 * (r.word.length + 1) + 4 * paddingRunBudget r + 12

/-- The raw tagged request is processed by a single uniform ordinary machine. -/
noncomputable def prepareMachine :
    WordFunction OutputRequest OutputRequest.word (fun r => frame r.padded) prepareBudget := by
  let f : WordFunction OutputRequest OutputRequest.word (fun r => frame (arithmeticInput r.word))
      (fun r => 400 * (r.word.length + 1)) :=
    ⟨arithmeticFraming.program, fun r => arithmeticFraming.realizes r.word⟩
  have h := Program.WordFunction.pipe f paddingArithmeticMachine
  convert h using 1
  funext r
  simp [prepareBudget]
  ring

/-- The padding really supplies at least `n` cells before the second arithmetic initialization. -/
theorem padded_length_ge_n (d : Input) : d.n ≤ (OutputRequest.padded (.inr d)).length := by
  simp only [OutputRequest.padded, Input.padded, List.length_cons, List.length_append, List.length_replicate]
  omega

end NearQuarticWires.StageOutput
