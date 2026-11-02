import Proof.Quartic.StageTupleTermPrice.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.RepairOrdinary.SignedSortKey (binary_length)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open StageTuple StagePrint

/-- `prop:time`, paper/paper.tex: actual
fixed-width row streams contain one field frame per real native or
suffix-tuple coordinate, including an empty stream when the pool is empty. -/
theorem field_records_length (L N : ℕ) (rows : List (List ℤ))
    (h : ∀row∈rows,row.length=N) :
    ((fieldRecords L rows).flatMap frame).length=rows.length*N*(2*L+1) := by
  rw [←fieldsRecs_eq_records]
  exact fieldsRecs_length L N rows h

theorem child_word_length (r : ChildTupleRequest) : r.word.length=
    2*(r.children.length*r.N*(2*r.L+1)+1+
      (r.tuples.length*r.M*(2*r.L+1)+1)+r.N+r.M+r.children.length+r.tuples.length)+11 := by
  simp only [ChildTupleRequest.word,Top.loadRec,List.length_append,frame_length,List.length_nil,
    List.length_replicate,recStream_map_length,fieldNums_length _ _ r.children_length,
    fieldNums_length _ _ r.tuples_length]
  ring

theorem tuple_records_length (r : ChildTupleRequest) :
    ((tupleRecords r).flatMap frame).length=
      r.children.length*r.tuples.length*(r.N+r.M)*(2*r.L+1) := by
  unfold tupleRecords
  rw [field_records_length _ (r.N+r.M) _
    (newT_mem_length _ _ _ _ r.children_length r.tuples_length),newT_length]

/-- `prop:time`, paper/paper.tex: the
actual Stack input includes its real tuple fields, all five fixed
constants and its four actual unary dimension headers. -/
theorem stack_word_length (r : StackRequest) : r.word.length=
    2*(r.tuples.length*(r.m*(r.s+1))*(2*(r.W+1)+1)+1+
      5*(2*(r.W+1)+1)+r.m*(r.s+1)+(r.s+1)+r.m+r.tuples.length)+11 := by
  simp only [StackRequest.word,Top.loadRec,List.length_append,frame_length,List.length_nil,
    List.length_replicate,recStream_map_length,binary_length,stackNums_length]
  ring

theorem stack_field_records_length (r : StackRequest) :
    ((fieldRecords (r.W+1) (r.tuples.map List.flatten)).flatMap frame).length=
      r.tuples.length*(r.m*(r.s+1))*(2*(r.W+1)+1) := by
  rw [←fieldsRecs_eq_records,fieldsRecs_length _ (r.m*(r.s+1))]
  · rw [List.length_map]
  · intro row hr
    obtain ⟨rows,hrows,rfl⟩:=List.mem_map.mp hr
    have hh:=flatten_take_length (r.s+1) rows rows.length (r.row_length rows hrows) le_rfl
    rw [List.take_of_length_le le_rfl,r.tuple_length rows hrows] at hh
    exact hh

end NearQuarticWires.StageTupleTermPrice
