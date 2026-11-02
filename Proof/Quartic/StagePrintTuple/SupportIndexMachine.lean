import Proof.Quartic.StagePrintTuple.SupportIndex
import Proof.Quartic.StagePrep.FrameProgram
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces (wordFunction_of_wmx)

/-- `prop:time`, paper/paper.tex: selected-variable
arithmetic uses only the per-support packet and pays the actual output
framing translation, independently of the complete Terms source. -/
def SupportIndexRequest.arithmeticBudget (r : SupportIndexRequest) : ℕ :=
  budgetOf VV 4 r.word.length (3 * r.steps (ctxOf 4 r.word []) + 2)

/-- `lem:print`, paper/paper.tex: the real binary
selection program produces the exact framed original variable codec
from an actual finite arithmetic input packet. -/
noncomputable def supportIndexArithmeticWordFunction :
    WordFunction SupportIndexRequest (fun r => StageOutput.arithmeticInput r.word)
      (fun r => frame r.output) SupportIndexRequest.arithmeticBudget :=
  wordFunction_of_wmx (prog 4 (StagePrep.framedProgram supportIndexProgram)) sOUT (by simp)
    (fun r => capOf 4 r.word [] (3 * r.steps (ctxOf 4 r.word []) + 2)) (by
      intro r
      let C := ctxOf 4 r.word []
      have hW : r.word.length + 3 ≤ C.Wd := by
        change r.word.length + 3 ≤ (r.word.length + 4) ^ 4
        exact (by omega : r.word.length + 3 ≤ r.word.length + 4).trans
          (Nat.le_self_pow (by decide) _)
      obtain ⟨b, n, he, hn, ho⟩ := supportIndexProgram_run C r rfl hW
      have hf := StagePrep.framedProgram_spec he
      obtain ⟨τ, hr, hout, hh, hv⟩ := prog_spec 4 (by decide)
        (StagePrep.framedProgram supportIndexProgram) r.word [] hf (3 * r.steps C + 2) (by omega)
      exact ⟨τ, hr, by simpa only [StagePrep.framedState, ho] using hout, hh, hv⟩)

/-- `prop:time`, paper/paper.tex: input framing,
actual prefix selection and output framing have additive physical cost. -/
def SupportIndexRequest.budget (r : SupportIndexRequest) : ℕ :=
  1600 * (r.word.length + 1) + 4 * r.arithmeticBudget + 12

/-- `lem:print`, paper/paper.tex: the actual
cold support-index word function returns exactly the original variable,
with no selected-atom or predecoded-role input premise. -/
noncomputable def supportIndexWordFunction :
    WordFunction SupportIndexRequest SupportIndexRequest.word (fun r => frame r.output)
      SupportIndexRequest.budget := by
  let f : WordFunction SupportIndexRequest SupportIndexRequest.word
      (fun r => frame (StageOutput.arithmeticInput r.word))
      (fun r => 400 * (r.word.length + 1)) :=
    ⟨StageOutput.arithmeticFraming.program,
      fun r => StageOutput.arithmeticFraming.realizes r.word⟩
  convert Program.WordFunction.pipe f supportIndexArithmeticWordFunction using 1
  funext r
  simp only [SupportIndexRequest.budget]
  ring

end NearQuarticWires.StageTuple
