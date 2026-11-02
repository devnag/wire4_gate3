import Proof.Quartic.StagePrintTuple.Coefficient
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces (wordFunction_of_wmx)

/-- `prop:time`, paper/paper.tex: the isolated
signed-field converter's ordinary binary arithmetic clock uses its own
finite coefficient packet, independently of the complete Terms source. -/
def CoefficientRequest.arithmeticBudget (r : CoefficientRequest) : ℕ :=
  budgetOf VV 4 r.word.length r.steps

/-- `lem:print`, paper/paper.tex: the actual
binary coefficient machine emits its complete fixed native signed field
from a real finite arithmetic input with no prepared registers. -/
noncomputable def coefficientArithmeticWordFunction :
    WordFunction CoefficientRequest (fun r => StageOutput.arithmeticInput r.word)
      CoefficientRequest.output CoefficientRequest.arithmeticBudget :=
  wordFunction_of_wmx (prog 4 coefficientProgram) sOUT (by simp)
    (fun r => capOf 4 r.word [] r.steps) (by
      intro r
      let C := ctxOf 4 r.word []
      have hW : r.word.length + 3 ≤ C.Wd := by
        change r.word.length + 3 ≤ (r.word.length + 4) ^ 4
        exact (by omega : r.word.length + 3 ≤ r.word.length + 4).trans
          (Nat.le_self_pow (by decide) _)
      obtain ⟨b, n, he, hn, ho⟩ := coefficientProgram_run C r rfl hW
      obtain ⟨τ, hr, hout, hh, hv⟩ := prog_spec 4 (by decide) coefficientProgram r.word [] he r.steps hn
      exact ⟨τ, hr, by simpa only [ho] using hout, hh, hv⟩)

/-- `prop:time`, paper/paper.tex: physical
arithmetic-input framing and the actual signed-field program compose
with additive cold-machine budgets. -/
def CoefficientRequest.budget (r : CoefficientRequest) : ℕ :=
  1600 * (r.word.length + 1) + 4 * r.arithmeticBudget + 12

/-- `lem:print`, paper/paper.tex: one genuine
cold word function converts the literal width/coefficient packet into
its exact double-framed native signed field, including all preparation. -/
noncomputable def coefficientWordFunction :
    WordFunction CoefficientRequest CoefficientRequest.word CoefficientRequest.output
      CoefficientRequest.budget := by
  let f : WordFunction CoefficientRequest CoefficientRequest.word
      (fun r => frame (StageOutput.arithmeticInput r.word))
      (fun r => 400 * (r.word.length + 1)) :=
    ⟨StageOutput.arithmeticFraming.program,
      fun r => StageOutput.arithmeticFraming.realizes r.word⟩
  convert Program.WordFunction.pipe f coefficientArithmeticWordFunction using 1
  funext r
  simp only [CoefficientRequest.budget]
  ring

end NearQuarticWires.StageTuple
