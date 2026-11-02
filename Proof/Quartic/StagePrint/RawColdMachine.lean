import Proof.Quartic.StagePrint.RawColdRun
import Proof.Quartic.StagePrep.FrameProgram
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.StagePrint.OriginalChildPrinter
import Proof.Quartic.Program.Pipe

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (wordFunction_of_wmx)
open NearCubicGates.Close.Expand.PolyTab
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `prop:time`, paper/paper.tex: the cold source formatter pays for framing, explicit arithmetic setup and the complete dense scan. -/
def coldArithmeticBudget (r : OriginalChildRequest) : ℕ :=
  budgetOf VV 4 (originalGateSource r).length
    (3*coldOriginalSteps (ctxOf 4 (originalGateSource r) []) r+2)

/-- `lem:print`, paper/paper.tex: an ordinary machine constructs the original child input from the actual signed gate source, including all initialization and field emission. -/
noncomputable def coldArithmeticMachine :
    WordFunction OriginalChildRequest
      (fun r=>StageOutput.arithmeticInput (originalGateSource r))
      (fun r=>frame r.word) coldArithmeticBudget :=
  wordFunction_of_wmx (prog 4 (StagePrep.framedProgram coldOriginalGate)) sOUT (by simp)
    (fun r=>capOf 4 (originalGateSource r) []
      (3*coldOriginalSteps (ctxOf 4 (originalGateSource r) []) r+2)) (by
      intro r
      let C:=ctxOf 4 (originalGateSource r) []
      have hW : (originalGateSource r).length+3≤C.Wd := by
        change (originalGateSource r).length+3≤((originalGateSource r).length+4)^4
        exact (by omega : (originalGateSource r).length+3≤(originalGateSource r).length+4).trans
          (Nat.le_self_pow (by norm_num) _)
      obtain ⟨b,n,he,hn,ho⟩:=coldOriginalGate_run C r rfl hW
      have hf:=StagePrep.framedProgram_spec he
      obtain ⟨τ,hr,hout,hh,hv⟩:=prog_spec 4 (by norm_num)
        (StagePrep.framedProgram coldOriginalGate) (originalGateSource r) [] hf
        (3*coldOriginalSteps C r+2) (by omega)
      exact ⟨τ,hr,by simpa only [StagePrep.framedState,ho] using hout,hh,hv⟩)

/-- `prop:time`, paper/paper.tex: the unprepared source includes its own paid ordinary input-framing pass. -/
def coldSourceBudget (r : OriginalChildRequest) : ℕ :=
  1600*((originalGateSource r).length+1)+4*coldArithmeticBudget r+12

/-- `lem:print`, paper/paper.tex: the original signed source, rather than a supplied child tape, is the input of one uniform ordinary formatter. -/
noncomputable def coldSourceMachine :
    WordFunction OriginalChildRequest originalGateSource (fun r=>frame r.word) coldSourceBudget := by
  let f : WordFunction OriginalChildRequest originalGateSource
      (fun r=>frame (StageOutput.arithmeticInput (originalGateSource r)))
      (fun r=>400*((originalGateSource r).length+1)) :=
    ⟨StageOutput.arithmeticFraming.program,fun r=>StageOutput.arithmeticFraming.realizes (originalGateSource r)⟩
  have h:=NearQuarticWires.Program.WordFunction.pipe f coldArithmeticMachine
  convert h using 1
  funext r
  simp [coldSourceBudget]
  ring

/-- `prop:time`, paper/paper.tex: formatting and original disjoint decomposition are both charged before any star-corner pullback. -/
def originalSourceChildrenBudget (r : OriginalChildRequest) : ℕ :=
  4*coldSourceBudget r+4*(2*r.budget+2)+12

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the concrete original gate word is physically decomposed, with no child-list input assumption. -/
noncomputable def originalSourceChildren :
    WordFunction OriginalChildRequest originalGateSource OriginalChildRequest.output
      originalSourceChildrenBudget := by
  exact NearQuarticWires.Program.WordFunction.pipe coldSourceMachine originalChildPrinter

end NearQuarticWires.StagePrint.RawBits
