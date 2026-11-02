import Proof.Quartic.StageNativeMiddleMap.Call
import Proof.Quartic.Control.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

theorem final_fresh (p : Program) :
    (∀ i : Fin 19,external p i≠final p) ∧ (∀ j,bank p j≠final p) := by
  constructor
  · intro i h
    have hh:=congrArg Fin.val h
    change i.val=p.tapeCount+19 at hh
    omega
  · intro j h
    have hh:=congrArg Fin.val h
    change 19+j.val=p.tapeCount+19 at hh
    omega

/-- `lem:print`, paper/paper.tex: the
whole actual callee run, copying and cleanup leave the fresh final
output tape exactly empty before final record emission. -/
theorem call_avoids_final (p : Program) : WMX.Avoids (final p) (callProgram p) := by
  have hF:=(final_fresh p).1
  have hB:=(final_fresh p).2
  simp [WMX.Avoids,WM.Avoids,callProgram,StagePrint.callAppendProgram,
    callP,cleanP,eraseP,WMX.machZ,Site.swept,Site.input,
    NearCubicGates.Close.WorkerArith.guardP,NearCubicGates.Close.WorkerArith.tallyP,
    NearCubicGates.Close.WorkerArith.twoOnes,NearCubicGates.Close.WorkerArith.clearSelfP,
    BinW.width,BinW.widthW,BinW.widthLoop,BinW.backLoop,
    StagePrint.appendFrameReset,CounterAsm.frameCopy,
    NearCubicGates.Close.Recovery.HTParts.pairLoop,NearCubicGates.Close.Recovery.HTParts.cellE,
    emitC,WM.fwdC,WM.rewind,WM.move,WM.clear,
    WMX.wr,WMX.fwd,WMX.bwd,WMX.inc,WMX.dec,WMX.skip,site,hF,hB]
  constructor
  · intro j
    refine Fin.addCases (fun k=>?_) (fun _=>?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (fun k=>?_) (fun _=>?_) k
      · simpa only [Fin.addCases_left] using hB k
      · simpa only [Fin.addCases_right] using hF 14
    · simpa only [Fin.addCases_right] using hF 16
  · intro j
    refine Fin.addCases (fun k=>?_) (fun _=>?_) j
    · simp only [Fin.addCases_left]
      refine Fin.addCases (fun k=>?_) (fun _=>?_) k
      · simp only [Fin.addCases_left]
        refine Fin.addCases (fun k=>?_) (fun _=>?_) k
        · simpa only [Fin.addCases_left] using hB k
        · simpa only [Fin.addCases_right] using hF 14
      · simpa only [Fin.addCases_right] using hF 15
    · simpa only [Fin.addCases_right] using hF 16

end NearQuarticWires.StageNativeMiddleMap
