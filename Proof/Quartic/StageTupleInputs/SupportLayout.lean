import Proof.Quartic.StagePrintTuple.InputContracts
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearQuarticWires.StageTupleInputs

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close NearCubicGates.Close.Interfaces
open StageTuple

/-- `lem:print`, paper/paper.tex: the actual
retained count prefix is already passed; the remaining source is exactly
the unchanged original variable codecs with their genuine final marker. -/
theorem supportSource_split (support : List ℕ) :
    frame (listWord natWord support)=marks (natWord support.length)++
      frame (support.flatMap natWord) := by
  simp only [listWord,Codec.frame_eq_marks,Streaming.marks_append,List.append_assoc]

theorem supportInput_frame (r : SupportIndexRequest) :
    frame r.word=marks (natWord r.index.val)++marks (natWord r.support.length)++
      marks (r.support.flatMap natWord)++[false] := by
  simp only [SupportIndexRequest.word,listWord,Codec.frame_eq_marks,
    Streaming.marks_append,List.append_assoc]

theorem bitLength_le (v : ℕ) : natBitLength v≤v+1 := by
  unfold natBitLength
  have hh:=Nat.log_le_self 2 v
  omega

theorem supportMagnitude_bounds (r : SupportIndexRequest) :
    r.support.length+1≤ supportInputMagnitude r ∧ r.index.val+1≤ supportInputMagnitude r ∧
      (r.support.flatMap natWord).length≤ supportInputMagnitude r ∧
      20≤ supportInputMagnitude r := by
  unfold supportInputMagnitude
  simp only [listWord,List.length_append]
  omega

theorem supportPacket_length (r : SupportIndexRequest) :
    (frame r.word).length≤8*supportInputMagnitude r := by
  rw [supportInput_frame]
  have hi:=bitLength_le r.index.val
  have hm:=bitLength_le r.support.length
  simp only [List.length_append,Codec.marks_length,List.length_singleton,
    NearCubicGates.Close.Dispatch.natWord_length]
  unfold supportInputMagnitude
  simp only [listWord,List.length_append]
  omega

end NearQuarticWires.StageTupleInputs
