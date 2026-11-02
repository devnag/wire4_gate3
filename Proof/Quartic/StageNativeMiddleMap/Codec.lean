import Proof.Quartic.StageNativeMiddleMap.Layout
import Proof.Quartic.StageNativeKids.NaturalField

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close

/-- `lem:print`, paper/paper.tex: the
unchanged eleven-field record consists of three nonempty literal
fields followed by exactly eight empty-field delimiters. -/
theorem word_eq (q : ℕ) (payload : List Bool) (count : ℕ) :
    StagePrint.NativeMiddle.word q payload count=
      frame (natWord q)++frame (frame payload)++frame (natWord count)++List.replicate 8 false := by
  simp only [StagePrint.NativeMiddle.word,Top.loadRec,Codec.frame_eq_marks,
    marks,List.flatMap_nil,List.nil_append,List.replicate_succ,List.replicate_zero,List.append_assoc]
  rfl

theorem frame_word_eq (q : ℕ) (payload : List Bool) (count : ℕ) :
    frame (StagePrint.NativeMiddle.word q payload count)=
      marks (frame (natWord q))++marks (frame (frame payload))++marks (frame (natWord count))++
        marks (List.replicate 8 false)++[false] := by
  rw [word_eq,Codec.frame_eq_marks]
  simp only [Streaming.marks_append,List.append_assoc]

theorem word_length (q : ℕ) (payload : List Bool) (count : ℕ) :
    (StagePrint.NativeMiddle.word q payload count).length=
      2*((natWord q).length+(frame payload).length+(natWord count).length)+11 := by
  rw [word_eq]
  simp only [List.length_append,frame_length,List.length_replicate]
  ring

end NearQuarticWires.StageNativeMiddleMap
