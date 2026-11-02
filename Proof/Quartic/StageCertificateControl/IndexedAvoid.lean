import Proof.Quartic.StageCertificateControl.IndexedLayout
import Proof.Quartic.Control.Frame

/-!
# Freshness of the final indexed preprocessing output

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
the index load, actual scheduler call/erase, nor binary threshold
extraction writes or moves the fresh final output. Exact output
freshness is therefore retained through the physical machine calls. -/
theorem indexedPrior_avoids_final (p : Program) :
    WMX.Avoids (indexedFinal p) (indexedLoadProgram p) ∧
    WMX.Avoids (indexedFinal p) (indexedScheduleProgram p) ∧
    WMX.Avoids (indexedFinal p) (indexedThresholdProgram p) := by
  have hF := (indexedFinal_fresh p).1
  have hB := (indexedFinal_fresh p).2
  constructor
  · simp [WMX.Avoids,WM.Avoids,indexedLoadProgram,readNatM,unaryBody,
      NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.bitBody,preE,addTo,dbl,dblLoop,
      copyPreparation,copyPayload,copyLoop,preEmit,Codec.emitScanned,finishMarkedCopy,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,
      emitC,emitPair,WM.fwdC,WM.rewind,WM.move,WM.clear,WMX.bwd,WMX.fwd,WMX.inc,WMX.skip,
      indexedSite,Site.input,hF,hB]
  constructor
  · simp [WMX.Avoids,WM.Avoids,indexedScheduleProgram,StagePrint.callAppendProgram,
      callP,cleanP,eraseP,WMX.machZ,Site.swept,Site.input,
      NearCubicGates.Close.WorkerArith.guardP,NearCubicGates.Close.WorkerArith.tallyP,
      NearCubicGates.Close.WorkerArith.twoOnes,NearCubicGates.Close.WorkerArith.clearSelfP,
      BinW.width,BinW.widthW,BinW.widthLoop,BinW.backLoop,
      StagePrint.appendFrameReset,CounterAsm.frameCopy,
      NearCubicGates.Close.Recovery.HTParts.pairLoop,NearCubicGates.Close.Recovery.HTParts.cellE,
      openCopiedFrame,returnCopiedFrame,measuredUnframe,Codec.unframeW,Codec.unframeCell,Codec.repLoop,
      selectMetadata,copyMetadataPrefix,copyMetadataRecord,copyRawFields,copyNatM,copyUnary,copyBit,
      unaryBody,preE,finishMarkedCopy,Control.incTimes,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,
      halveM,halveLoop,emitC,emitPair,WM.fwdC,WM.rewind,WM.move,WM.clear,
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

  · simp [WMX.Avoids,WM.Avoids,indexedThresholdProgram,measuredUnframe,
      Codec.unframeW,Codec.unframeCell,Codec.repLoop,
      copyThresholdFields,copyFixedFields,copyRawFields,copyNatM,copyUnary,copyBit,unaryBody,preE,Control.incTimes,
      finishMarkedCopy,NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,
      halveM,halveLoop,emitC,emitPair,WM.fwdC,WM.rewind,WM.move,WM.clear,WMX.inc,WMX.skip,hF]

end NearQuarticWires.StageCertificateControl
