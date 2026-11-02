import Proof.Quartic.StagePrintTuple.StackContract

set_option autoImplicit false

namespace NearQuarticWires.StageStackInput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageTuple

def tupleBytes (r : StagePrint.StackRequest) : List Bool :=
  (fieldRecords (r.W+1) (r.tuples.map List.flatten)).flatMap frame

def constantFields (r : StagePrint.StackRequest) : List (List Bool) :=
  [frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),
    frame (binary (r.W+1) (encS r.coefficient)),frame (binary (r.W+1) 2)]

def dimensions (r : StagePrint.StackRequest) : List ℕ :=
  [r.m*(r.s+1),r.s+1,r.m,r.tuples.length]

/-- `lem:print`, paper/paper.tex: the exact
existing Stack request has one tuple field, five genuine cached fields,
four computed unary fields and the unchanged final empty field. -/
theorem stackInput_frame (r : StagePrint.StackRequest) :
    frame r.word=marks (frame (tupleBytes r++[false]))++
      (constantFields r).flatMap (fun bits=>marks (frame bits))++
      unaryHeaderBytes (dimensions r)++marks [false]++[false] := by
  simp [StagePrint.StackRequest.word,StagePrint.StackRequest.nums,
    recStream_fieldNums,fieldsRecs_eq_records,tupleBytes,constantFields,dimensions,
    Top.loadRec,Codec.frame_eq_marks,unaryHeaderBytes,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,marks,List.append_assoc]

theorem constantFields_length (r : StagePrint.StackRequest) :
    ((constantFields r).flatMap (fun bits=>marks (frame bits))).length=40*r.W+70 := by
  simp only [constantFields,List.flatMap_cons,List.flatMap_nil,List.length_append,
    Codec.marks_length,frame_length,binary_length,List.length_nil]
  omega

theorem unaryBytes_length (values : List ℕ) :
    (unaryHeaderBytes values).length=4*values.sum+2*values.length := by
  induction values with
  | nil=>simp [unaryHeaderBytes]
  | cons v vs ih=>
      simp only [unaryHeaderBytes,List.flatMap_cons,List.length_append,Codec.marks_length,
        frame_length,List.length_replicate,List.sum_cons,List.length_cons] at *
      omega

/-- `prop:time`, paper/paper.tex: the actual
serialized call length contains only the current tuple segment and its
fixed fields/dimensions, never the retained history prefix. -/
theorem stackInput_length (r : StagePrint.StackRequest) :
    (frame r.word).length=4*(tupleBytes r).length+40*r.W+
      4*(r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length)+87 := by
  rw [stackInput_frame]
  simp only [List.length_append,Codec.marks_length,frame_length,
    constantFields_length,unaryBytes_length,dimensions,List.sum_cons,List.sum_nil,
    List.length_cons,List.length_nil]
  omega

end NearQuarticWires.StageStackInput
