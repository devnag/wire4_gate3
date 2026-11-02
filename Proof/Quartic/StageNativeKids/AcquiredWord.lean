import Proof.Quartic.StageNativeKids.Request

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageTuple

/-- `lem:print`, paper/paper.tex: the
first five retained fields are exactly the nonempty original source,
affine prefix, binary context, actual atom and target output width. -/
def NativeKidsRequest.prefixFields (r : NativeKidsRequest) : List (List Bool) :=
  [r.sourceFields 0, r.sourceFields 1, r.sourceFields 2, r.sourceFields 3, r.sourceFields 4]

/-- `lem:print`, paper/paper.tex: the
acquired role payload contains only the computed original occurrence
and the exact child-independent affine header. -/
def NativeKidsRequest.rolePayload (r : NativeKidsRequest) : List Bool :=
  natWord (r.toRowContext.originalIndex r.atom).val ++ r.toRowContext.rowHeader r.atom

/-- `lem:print`, paper/paper.tex: the
next source record retains the five original fields and appends the
physically computed role result as its sixth field. -/
def NativeKidsRequest.acquiredWord (r : NativeKidsRequest) : List Bool :=
  Top.loadRec (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) r.rolePayload [] [] [] [] []

/-- `lem:print`, paper/paper.tex: six
literal empty fields terminate the original five-field source prefix. -/
theorem source_prefix (r : NativeKidsRequest) :
    r.word = r.prefixFields.flatMap frame ++ List.replicate 6 false := by
  change Top.loadRec (r.sourceFields 0) (r.sourceFields 1) (r.sourceFields 2)
    (r.sourceFields 3) (r.sourceFields 4) [] [] [] [] [] [] = _
  simp only [Top.loadRec, NativeKidsRequest.prefixFields,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    show frame ([] : List Bool) = [false] from rfl,
    List.replicate_succ, List.replicate_zero, List.append_assoc]
  rfl

/-- `lem:print`, paper/paper.tex: every
retained source prefix field has a real first marker, including an
actual zero atom or empty original occurrence bank. -/
theorem prefixFields_nonempty (r : NativeKidsRequest) :
    ∀ field ∈ r.prefixFields, field ≠ [] := by
  have nat_nonempty (v : ℕ) : natWord v ≠ [] := by
    intro h
    have hh := congrArg List.length h
    rw [NearCubicGates.Close.CounterAsm.natWord_len] at hh
    simp only [List.length_nil] at hh
    omega
  intro field hf
  simp only [NativeKidsRequest.prefixFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · simp only [NativeKidsRequest.sourceFields, Matrix.cons_val_zero]
    have h := NearCubicWires.RepairOrdinary.frame_length (NearCubicGates.Close.Interfaces.callWord r.header.call)
    intro he
    rw [he] at h
    simp only [List.length_nil] at h
    omega
  · change frame _ ≠ []
    intro he
    have h := congrArg List.length he
    rw [NearCubicWires.RepairOrdinary.frame_length] at h
    simp only [List.length_nil] at h
    omega
  · change r.contextWord ≠ []
    unfold NativeKidsRequest.contextWord
    intro h
    have hh := congrArg List.length h
    rw [List.length_append, NearCubicGates.Close.CounterAsm.natWord_len] at hh
    simp only [List.length_nil] at hh
    omega
  · exact nat_nonempty r.atom.val
  · exact nat_nonempty r.outputWidth

/-- `lem:print`, paper/paper.tex: the
acquired source is the original nonempty prefix followed by the actual
role frame and five literal empty fields, all in their original order. -/
theorem acquiredWord_frame (r : NativeKidsRequest) :
    frame r.acquiredWord = Streaming.marks (r.prefixFields.flatMap frame) ++
      Streaming.marks (frame r.rolePayload) ++ Streaming.marks (List.replicate 5 false) ++ [false] := by
  have hw : r.acquiredWord = r.prefixFields.flatMap frame ++
      frame r.rolePayload ++ List.replicate 5 false := by
    simp only [NativeKidsRequest.acquiredWord, NativeKidsRequest.prefixFields,
      Top.loadRec, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      show frame ([] : List Bool) = [false] from rfl,
      List.replicate_succ, List.replicate_zero, List.append_assoc]
    rfl
  rw [hw, NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [Streaming.marks_append, List.append_assoc]

end NearQuarticWires.StageNativeKids
