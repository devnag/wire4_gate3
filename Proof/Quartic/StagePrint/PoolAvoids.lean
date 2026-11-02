import Proof.Quartic.StagePrint.PoolLoop
import Proof.Quartic.Control.Frame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the final framed original-child stream occupies a tape outside every reusable work bank. -/
def poolFinal (p : Program) : Fin (p.tapeCount+6) := ⟨p.tapeCount+5,by omega⟩

/-- `lem:print`, paper/paper.tex: every counted original-child call leaves the final stream physically untouched. -/
theorem poolLoop_avoids (p : Program) : WMX.Avoids (poolFinal p) (poolLoopProgram p) := by
  simp [WMX.Avoids, WM.Avoids, poolLoopProgram,poolOccurrenceProgram,poolOccurrence,
    writeIndexedInput,writeNatM,bitLenM,prefixM,payM,payBody,onesLoop,emitPair,
    halveM,halveLoop,lenLoop,NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,WM.clear,WM.move,
    copyLoop,preEmit,emitC,WM.fwdC,WM.rewind,
    NearCubicGates.Close.Codec.emitScanned,NearCubicGates.Close.Codec.rewindLoop,
    callAppendProgram,appendFrameReset,CounterAsm.frameCopy,
    NearCubicGates.Close.Recovery.HTParts.pairLoop,NearCubicGates.Close.Recovery.HTParts.cellE,
    callP,cleanP,eraseP,WMX.machZ,
    NearCubicGates.Close.WorkerArith.guardP,NearCubicGates.Close.WorkerArith.tallyP,
    NearCubicGates.Close.WorkerArith.clearSelfP,NearCubicGates.Close.WorkerArith.twoOnes,
    BinW.width,BinW.widthW,BinW.widthLoop,BinW.backLoop,
    WMX.fwd,WMX.bwd,WMX.wr,WMX.inc,WMX.dec,WMX.skip,
    Site.input,Site.swept,poolSite,poolSource,poolOutput,poolFinal,poolBank,Fin.ext_iff]
  and_intros
  all_goals (repeat' apply addCases_val (P := fun v=>¬v=p.tapeCount+5))
  all_goals try simp [WM.Avoids,poolBank]
  all_goals omega

end NearQuarticWires.StagePrint
