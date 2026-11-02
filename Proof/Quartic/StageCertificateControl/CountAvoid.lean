import Proof.Quartic.StageCertificateControl.Capacity

/-!
# The count computation preserves the fresh certificate output

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: count
serialization, decoding and bank erasure neither write nor move the
fresh final output stream used by the complete native table pool. -/
theorem poolCount_avoids_final (p q : Program) (hq : q.tapeCount≤p.tapeCount) :
    WMX.Avoids (StagePrint.poolFinal p) (poolCountProgram p q hq) := by
  have hp := p.twoTapes
  have hq2 := q.twoTapes
  have hb (j : Fin q.tapeCount) : (countBankSite p q hq).bank j≠StagePrint.poolFinal p := by
    intro h
    have hh := congrArg Fin.val h
    change 5+j.val=p.tapeCount+5 at hh
    have hj := j.isLt
    omega
  have hx := hb q.outputTape
  unfold poolCountProgram countCallProgram
  refine ⟨?_,?_,?_,?_⟩
  · simp [WMX.Avoids,WM.Avoids,Codec.copyRW,Codec.copyFrameW,Codec.copyPairW,
      Codec.dupR,emitC,WM.fwdC,WM.rewind,WM.move,
      countBankSite,Site.input,StagePrint.poolSource,StagePrint.poolFinal,StagePrint.poolBank,
      NearCubicGates.Close.WorkerArith.inTape,Fin.ext_iff]
    omega
  · simp [WMX.Avoids,WM.Avoids,callP,WMX.machZ,
      NearCubicGates.Close.WorkerArith.guardP,NearCubicGates.Close.WorkerArith.tallyP,
      NearCubicGates.Close.WorkerArith.twoOnes,BinW.width,BinW.widthW,BinW.widthLoop,BinW.backLoop,
      WM.rewind,WMX.wr,WMX.fwd,WMX.inc,WMX.dec,WMX.skip,Site.input,countBankSite,
      StagePrint.poolFinal,StagePrint.poolBank,Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬v=p.tapeCount+5)))
    all_goals first | omega | (intro j;have hj := j.isLt;simp [StagePrint.poolBank];omega) | simp
  · simp [WMX.Avoids,WM.Avoids,readCountHeader,returnCountHeader,doubleHeaderLength,
      readNatM,unaryBody,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.bitBody,
      preE,addTo,dbl,dblLoop,bitLenM,halveM,halveLoop,lenLoop,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR,
      NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup,WM.clear,WM.move,WM.rewind,hx]
  · simp [WMX.Avoids,WM.Avoids,cleanP,eraseP,WMX.machZ,Site.swept,
      NearCubicGates.Close.WorkerArith.clearSelfP,WMX.wr,WMX.fwd,WMX.bwd,WMX.inc,WMX.dec,WMX.skip,
      WM.rewind,countBankSite,StagePrint.poolFinal,StagePrint.poolBank,Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬v=p.tapeCount+5)))
    all_goals first | omega | (intro j;have hj := j.isLt;simp [StagePrint.poolBank];omega) | (intro h;cases h)

end NearQuarticWires.StageCertificateControl
