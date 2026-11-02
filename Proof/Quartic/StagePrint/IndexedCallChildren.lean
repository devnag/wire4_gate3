import Proof.Quartic.StagePrint.RawIndexedCall
import Proof.Quartic.StagePrint.RawColdMachine
import Proof.Quartic.StagePrint.FramedOriginalChildren

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces (wordFunction_of_wmx)
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: a fourth-power bit workspace covers the exact call-scanning arithmetic. -/
theorem callSource_space (L : ℕ) : 5*(L+2)^2≤(L+4)^4 := by
  have h1 : (L+2)^2≤(L+4)^2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : 5≤(L+4)^2 := by rw [pow_two];nlinarith
  calc
    5*(L+2)^2≤5*(L+4)^2 := Nat.mul_le_mul_left _ h1
    _≤(L+4)^2*(L+4)^2 := Nat.mul_le_mul_right _ h2
    _=(L+4)^4 := by ring

/-- `prop:time`, paper/paper.tex: the complete cold call formatter has an explicit ordinary clock. -/
def IndexedCallGateRequest.arithmeticBudget {second : Bool} (r : IndexedCallGateRequest second) : ℕ :=
  budgetOf VV 4 r.source.length (3*r.steps (ctxOf 4 r.source [])+2)

/-- `lem:print`, paper/paper.tex: actual original call bytes and occurrence index produce the original sharp compiler input. -/
noncomputable def indexedCallArithmeticMachine (second : Bool) :
    WordFunction (IndexedCallGateRequest second)
      (fun r=>StageOutput.arithmeticInput r.source) (fun r=>frame r.child.word)
      IndexedCallGateRequest.arithmeticBudget :=
  wordFunction_of_wmx (prog 4 (StagePrep.framedProgram (indexedCallGate second))) sOUT (by simp)
    (fun r=>capOf 4 r.source [] (3*r.steps (ctxOf 4 r.source [])+2)) (by
      intro r
      let C:=ctxOf 4 r.source []
      have hspace : 5*(C.cw.length+2)^2≤C.Wd := callSource_space r.source.length
      obtain ⟨b,n,he,hn,ho⟩:=indexedCallGate_run C second r rfl hspace
      have hf:=StagePrep.framedProgram_spec he
      obtain ⟨τ,hr,hout,hh,hv⟩:=prog_spec 4 (by norm_num)
        (StagePrep.framedProgram (indexedCallGate second)) r.source [] hf
        (3*r.steps C+2) (by omega)
      exact ⟨τ,hr,by simpa only [StagePrep.framedState,ho] using hout,hh,hv⟩)

/-- `prop:time`, paper/paper.tex: literal input framing is included before call selection. -/
def IndexedCallGateRequest.sourceBudget {second : Bool} (r : IndexedCallGateRequest second) : ℕ :=
  1600*(r.source.length+1)+4*r.arithmeticBudget+12

/-- `lem:print`, paper/paper.tex: an entirely cold original-call selector, with both source bank choices supported. -/
noncomputable def indexedCallSourceMachine (second : Bool) :
    WordFunction (IndexedCallGateRequest second) IndexedCallGateRequest.source
      (fun r=>frame r.child.word) IndexedCallGateRequest.sourceBudget := by
  let f : WordFunction (IndexedCallGateRequest second) IndexedCallGateRequest.source
      (fun r=>frame (StageOutput.arithmeticInput r.source))
      (fun r=>400*(r.source.length+1)) :=
    ⟨StageOutput.arithmeticFraming.program,fun r=>StageOutput.arithmeticFraming.realizes r.source⟩
  have h:=NearQuarticWires.Program.WordFunction.pipe f (indexedCallArithmeticMachine second)
  convert h using 1
  funext r
  simp [IndexedCallGateRequest.sourceBudget]
  ring

/-- `prop:time`, paper/paper.tex: original-call scanning, exact decomposition, and output record framing are all paid. -/
def IndexedCallGateRequest.childrenBudget {second : Bool} (r : IndexedCallGateRequest second) : ℕ :=
  4*r.sourceBudget+4*(2*childFrameSteps r.child+2)+12

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the actual original-call occurrence yields its complete framed disjoint child stream before all corner pullbacks. -/
noncomputable def indexedCallChildren (second : Bool) :
    WordFunction (IndexedCallGateRequest second) IndexedCallGateRequest.source
      (fun r=>frame r.child.output) IndexedCallGateRequest.childrenBudget := by
  let g : WordFunction (IndexedCallGateRequest second) (fun r=>r.child.word)
      (fun r=>frame r.child.output) (fun r=>2*childFrameSteps r.child+2) :=
    ⟨framedOriginalChildPrinter.program,fun r=>framedOriginalChildPrinter.realizes r.child⟩
  exact NearQuarticWires.Program.WordFunction.pipe (indexedCallSourceMachine second) g

end NearQuarticWires.StagePrint.RawBits
