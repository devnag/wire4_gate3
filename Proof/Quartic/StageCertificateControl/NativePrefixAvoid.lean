import Proof.Quartic.StageCertificateControl.NativePrefixLayout
import Proof.Quartic.Control.Frame

/-!
# Physical output freshness around the whole native table call

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: neither
the actual binary-header load nor the whole native table call, copied
output and physical erasure writes or moves the fresh final stream. -/
theorem nativePrefixPrior_avoids_final (p : Program) :
    WMX.Avoids (indexedFinal p) (nativePrefixLoadProgram p) ∧
      WMX.Avoids (indexedFinal p) (nativePrefixCallProgram p) := by
  have hF := (indexedFinal_fresh p).1
  have hB := (indexedFinal_fresh p).2
  constructor
  · simp [WMX.Avoids,WM.Avoids,nativePrefixLoadProgram,copyNatM,copyUnary,copyBit,preE,
      copyPreparation,copyPayload,copyLoop,preEmit,Codec.emitScanned,finishMarkedCopy,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,
      emitC,emitPair,WM.fwdC,WM.rewind,WM.move,WM.clear,WMX.bwd,WMX.fwd,WMX.inc,WMX.skip,
      indexedSite,Site.input,hF,hB]
  · simp [WMX.Avoids,WM.Avoids,nativePrefixCallProgram,StagePrint.callAppendProgram,
      callP,cleanP,eraseP,WMX.machZ,Site.swept,Site.input,
      NearCubicGates.Close.WorkerArith.guardP,NearCubicGates.Close.WorkerArith.tallyP,
      NearCubicGates.Close.WorkerArith.twoOnes,NearCubicGates.Close.WorkerArith.clearSelfP,
      BinW.width,BinW.widthW,BinW.widthLoop,BinW.backLoop,
      StagePrint.appendFrameReset,CounterAsm.frameCopy,
      NearCubicGates.Close.Recovery.HTParts.pairLoop,NearCubicGates.Close.Recovery.HTParts.cellE,
      emitC,WM.fwdC,WM.rewind,WM.move,WM.clear,
      WMX.wr,WMX.fwd,WMX.bwd,WMX.inc,WMX.dec,WMX.skip,indexedSite,hF,hB]
    constructor
    · intro j
      refine Fin.addCases (fun k => ?_) (fun _ => ?_) j
      · simp only [Fin.addCases_left]
        refine Fin.addCases (fun k => ?_) (fun _ => ?_) k
        · simpa only [Fin.addCases_left] using hB k
        · simpa only [Fin.addCases_right] using hF 8
      · simpa only [Fin.addCases_right] using hF 10
    · intro j
      refine Fin.addCases (fun k => ?_) (fun _ => ?_) j
      · simp only [Fin.addCases_left]
        refine Fin.addCases (fun k => ?_) (fun _ => ?_) k
        · simp only [Fin.addCases_left]
          refine Fin.addCases (fun k => ?_) (fun _ => ?_) k
          · simpa only [Fin.addCases_left] using hB k
          · simpa only [Fin.addCases_right] using hF 8
        · simpa only [Fin.addCases_right] using hF 9
      · simpa only [Fin.addCases_right] using hF 10

end NearQuarticWires.StageCertificateControl
