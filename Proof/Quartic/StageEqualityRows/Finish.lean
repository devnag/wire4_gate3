import Proof.Quartic.StageEqualityRows.Naturals

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts
open StagePrint

def oddState (r : NativeStreamRequest) : WState 15 24 :=
  appendO (header3 r) 15 13 [true,false]
def bodyState (r : NativeStreamRequest) : WState 15 24 :=
  ((appendO (oddState r) 15 13 (marks (stream r))).setv 16 0).seth 2 (stream r).length

def finishProgram : WM 15 24 :=
  .seq (emitPair 15 13 false)
    (.seq (NearCubicGates.Close.Codec.frameStream 2 15 13 16) (emitC 15 13 false))

/-- `lem:print`, paper/paper.tex: output the
literal even-split flag and every original signed equality byte,
retaining their order inside one actual outer frame. -/
theorem finishProgram_run (r : NativeStreamRequest) :
    ∃ final,WExec (capacity r) finishProgram (header3 r) final (22*(stream r).length+26) ∧
      final.st 15=frame r.equalitySource := by
  have hw:=bitLength_le (width r)
  have hp:=bitLength_le r.fieldWidth
  have hg:=bitLength_le r.cuts.length
  have e1:=emitPair_spec (capacity r) (15 : Fin 16) 13 false (header3 r)
    (by simp [header3,header2,header1,appendO,copyReady,counted,adv,strideState,afterFields,afterWidth,loaded,lens,Nat.add_assoc])
    (by simp [header3,header2,header1,appendO,copyReady,counted_values,marks_length,
      NearCubicGates.Close.CounterAsm.natWord_len];unfold capacity;omega)
  have e2:=NearCubicGates.Close.Codec.frameStream_spec (capacity r) (2 : Fin 16) 15 (by decide)
    13 16 (by decide) (stream r) [] [] (oddState r)
    (by simp [oddState,header3,header2,header1,appendO,copyReady,counted,adv,strideState,
      afterFields,afterWidth,loaded,fields])
    (by simp [oddState,header3,header2,header1,appendO,copyReady])
    (by simp [oddState,header3,header2,header1,appendO,copyReady,counted,adv,strideState,
      afterFields,afterWidth,loaded,lens,Nat.add_assoc])
    (by simp [oddState,header3,header2,header1,appendO,copyReady])
    (by unfold capacity;omega)
    (by simp [oddState,header3,header2,header1,appendO,copyReady,counted_values,marks_length,
      NearCubicGates.Close.CounterAsm.natWord_len];unfold capacity;omega)
  have e2' : WExec (capacity r) (NearCubicGates.Close.Codec.frameStream 2 15 13 16)
      (oddState r) (bodyState r) (22*(stream r).length+1) := by simpa only [bodyState,List.length_nil,Nat.zero_add] using e2
  have e3:=NearCubicGates.Close.Codec.emitBit_spec (capacity r) (15 : Fin 16) 13 false (bodyState r)
    (by simp [bodyState,oddState,header3,header2,header1,appendO,copyReady,counted,adv,
      strideState,afterFields,afterWidth,loaded,lens,marks_length,Nat.add_assoc];omega)
    (by simp [bodyState,oddState,header3,header2,header1,appendO,copyReady,counted_values,marks_length,
      NearCubicGates.Close.CounterAsm.natWord_len];unfold capacity;omega)
  refine ⟨appendO (bodyState r) 15 13 [false],(e1.seq (e2'.seq e3)).mono (by omega),?_⟩
  simp only [bodyState,oddState,header3,header2,header1,appendO,WState.seth_st,WState.setv_st,
    Function.update_self]
  have hzero : (copyReady r).st 15=[] := by
    simp [copyReady,counted,adv,strideState,afterFields,afterWidth,loaded,lens]
  rw [hzero]
  unfold NativeStreamRequest.equalitySource EquationRowRaw.source EquationHeaderRead.word
    EquationHeaderRead.header NativeStreamRequest.equalityInput EquationRowCuts.stream
  simp [width,stream,NearCubicGates.Close.Codec.frame_eq_marks,NearCubicWires.RepairOrdinary.Streaming.marks_append,marks,List.append_assoc]

end NearQuarticWires.StageEqualityRows
