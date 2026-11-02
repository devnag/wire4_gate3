import Proof.Quartic.StagePrint.ChildRecordFrame

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: the complete original child stream is supplied in one actual outer frame for a subsequent record-processing pass. -/
noncomputable def framedOriginalChildPrinter :
    WordFunction OriginalChildRequest OriginalChildRequest.word
      (fun r=>frame r.output) (fun r=>2*childFrameSteps r+2) :=
  wordFunction_of_ideal childFrameProgram childFrameOut
    (by have h : 2≤childFrameTapes:=originalChildPrinter.program.twoTapes
        change childFrameTapes≠0
        omega)
    (fun r=>2*r.output.length+2) childFrameLens childFrameSteps
    (fun _=>le_rfl) (by
      intro r
      refine ⟨?_,childFrameProgram_run r⟩
      unfold childFrameLens
      rw [if_neg]
      intro h
      have hh:=congrArg Fin.val h
      change childFrameTapes=childFrameTapes+1 at hh
      omega)

/-- `prop:time`, paper/paper.tex: source serialization, original exact decomposition and record framing have their full sequential clock. -/
def sourceFramedChildrenBudget (r : OriginalChildRequest) : ℕ :=
  4*RawBits.coldSourceBudget r+4*(2*childFrameSteps r+2)+12

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: one uniform machine maps the actual original gate source to its framed disjoint-child stream, ready for physical pooling. -/
noncomputable def sourceFramedChildren :
    WordFunction OriginalChildRequest RawBits.originalGateSource
      (fun r=>frame r.output) sourceFramedChildrenBudget :=
  NearQuarticWires.Program.WordFunction.pipe RawBits.coldSourceMachine framedOriginalChildPrinter

end NearQuarticWires.StagePrint
