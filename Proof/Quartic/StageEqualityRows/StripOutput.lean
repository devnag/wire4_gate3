import Proof.Quartic.StageEqualityRows.StripBody

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.Recovery.HTParts NearCubicGates.Close.Expand.PolyTab
open StagePrint StagePrint.Downstream

def stripOutputProgram : WM 15 24 :=
  .seq (frameStream 1 15 13 16) (emitC 15 13 false)

/-- `lem:print`, paper/paper.tex: copy exactly
the measured weak-body suffix and frame it, after the real header scan;
all signed field bytes retain their original constructor order. -/
theorem stripOutput_run (r : NativeStreamRequest) :
    ∃ final,WExec (stripCapacity r) stripOutputProgram (bodyCopyReady r) final
      (22*(weakStream r).length+9) ∧ final.st 15=equalityRowsOutput r := by
  have hB:=weakStream_le r
  have e1:=frameStream_spec (stripCapacity r) (1 : Fin 16) 15 (by decide) 13 16 (by decide)
    (weakStream r) (temporaryHeader r) [] (bodyCopyReady r)
    (by simp [bodyCopyReady,bodyCounted,adv,headerReady,stripStride,columnCounted,widthRead,
      afterLeading,stripLoaded,temporaryWord_shape,temporaryHeader,List.append_assoc])
    (by simp [bodyCopyReady])
    (by simp [bodyCopyReady,bodyCounted,adv,headerReady,stripStride,columnCounted,widthRead,
      afterLeading,stripLoaded,stripStart,idealStart])
    (by simp [bodyCopyReady])
    (by unfold stripCapacity capacity;omega)
    (by simp [bodyCopyReady,bodyCounted_values];unfold stripCapacity capacity;omega)
  let a:=((appendO (bodyCopyReady r) 15 13 (NearCubicWires.RepairOrdinary.Streaming.marks (weakStream r))).setv 16 0).seth 1
    ((temporaryHeader r).length+(weakStream r).length)
  have e2:=emitBit_spec (stripCapacity r) (15 : Fin 16) 13 false a
    (by simp [a,appendO,bodyCopyReady,bodyCounted,adv,headerReady,stripStride,columnCounted,
      widthRead,afterLeading,stripLoaded,stripStart,idealStart])
    (by simp [a,appendO,bodyCopyReady,bodyCounted_values,
      NearCubicWires.RepairOrdinary.Streaming.marks_length];unfold stripCapacity capacity;omega)
  refine ⟨appendO a 15 13 [false],(e1.seq e2).mono (by omega),?_⟩
  simp [a,appendO,bodyCopyReady,bodyCounted,adv,headerReady,stripStride,columnCounted,
    widthRead,afterLeading,stripLoaded,stripStart,idealStart,equalityRowsOutput,weakStream,
    frame_eq_marks]

def stripBodyProgram : WM 15 24 :=
  .seq (CutScan.countRows 1 countRegisters)
    (.seq (.seq (dupR 1 16 17) (WM.rewind 1 1)) stripOutputProgram)
def bodySteps (r : NativeStreamRequest) : ℕ :=
  weakCountSteps r+(23*(weakStream r).length+6)+(22*(weakStream r).length+9)+2

/-- `lem:print`, paper/paper.tex: body extraction
includes the physical count, measured rewind and complete framed copy. -/
theorem stripBodyProgram_run (r : NativeStreamRequest) :
    ∃ final,WExec (stripCapacity r) stripBodyProgram (headerReady r) final (bodySteps r) ∧
      final.st 15=equalityRowsOutput r := by
  obtain ⟨final,he,ho⟩:=stripOutput_run r
  exact ⟨final,((bodyCounted_run r).seq ((bodyCopyReady_run r).seq he)).mono
    (by unfold bodySteps;omega),ho⟩

end NearQuarticWires.StageEqualityRows
