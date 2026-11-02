import Proof.Quartic.StagePrintTuple.RepeatLiteral
import Proof.Gates.Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- `lem:print`, paper/paper.tex: marking a
physically generated unary count doubles exactly its written bit count. -/
theorem marks_true_replicate (j : ℕ) :
    marks (List.replicate j true)=List.replicate (2*j) true := by
  change (List.replicate j true).flatMap (fun b=>[true,b])=_
  rw [List.flatMap_replicate]
  change (List.replicate j (List.replicate 2 true)).flatten=_
  rw [List.flatten_replicate_replicate]
  congr 1
  omega

/-- `lem:print`, paper/paper.tex: the actual
unary original-child index contributes all three required marker layers
and both inner delimiters to the cold eleven-field row input. -/
theorem nestedUnary_bytes (j : ℕ) :
    marks (frame (frame (List.replicate j true)))=
      List.replicate (8*j) true++[true,true,true,false,true,false] := by
  simp only [NearCubicGates.Close.Codec.frame_eq_marks,Streaming.marks_append,
    marks_true_replicate,show marks [false]=[true,false] from rfl,
    show marks [true,false]=[true,true,true,false] from rfl,
    List.append_assoc,List.cons_append,List.nil_append]
  congr 2
  omega

/-- `lem:print`, paper/paper.tex: repeating the
four-bit literal block writes exactly the eight marker bits per unit
needed for the original-child unary field. -/
theorem repeatedQuadruple_bytes (j : ℕ) :
    marks (List.replicate j [true,true,true,true]).flatten=List.replicate (8*j) true := by
  change marks (List.replicate j (List.replicate 4 true)).flatten=_
  rw [List.flatten_replicate_replicate,marks_true_replicate]
  congr 1
  omega

end NearQuarticWires.StageTuple
