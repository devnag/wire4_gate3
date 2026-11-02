import Proof.Quartic.StageNativeKids.TailRequest
import Proof.Quartic.StageNativeKids.MarkedCopy
import Proof.Quartic.StageResize.StreamCost
import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.CounterMachine.TabCallDock

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms.SInt
open StageNativeKids StageResize

def countWord (r : ResizeTailRequest) : List Bool := natWord r.stream.rows.length

def inputRecords (r : ResizeTailRequest) : List (List Bool) :=
  r.stream.rows.flatten.map (fun z=>binary r.stream.inputWidth (encS z))
def outputRecords (r : ResizeTailRequest) : List (List Bool) :=
  r.stream.rows.flatten.map (fun z=>binary r.stream.outputWidth (encS z))

/-- `lem:print`, paper/paper.tex: the actual
source consists of its original binary row count followed by the
unchanged width codec, signed field frames and final stream delimiter. -/
theorem source_shape (r : ResizeTailRequest) :
    r.word=countWord r++natWord r.stream.outputWidth++(inputRecords r).flatMap frame++[false] := by
  unfold ResizeTailRequest.word StreamResizeRequest.word countWord inputRecords
  rw [fieldsRecs_eq_numberRecords]
  simp only [numberRecords,List.flatMap_map,Function.comp_def,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the actual
raw resize output preserves every signed field frame in order. -/
theorem output_shape (r : ResizeTailRequest) : r.stream.output=(outputRecords r).flatMap frame := by
  unfold StreamResizeRequest.output outputRecords
  rw [fieldsRecs_eq_numberRecords]
  simp only [numberRecords,List.flatMap_map,Function.comp_def]

theorem inputRecords_nonempty (r : ResizeTailRequest) : ∀ bits∈inputRecords r,bits≠[] := by
  intro bits hb
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hb
  intro he
  have hl : (binary r.stream.inputWidth (encS z)).length=r.stream.inputWidth:=binary_length _ _
  rw [he] at hl
  have h:=r.stream.input_pos
  simp only [List.length_nil] at hl
  omega

theorem outputRecords_nonempty (r : ResizeTailRequest) : ∀ bits∈outputRecords r,bits≠[] := by
  intro bits hb
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hb
  intro he
  have hl : (binary r.stream.outputWidth (encS z)).length=r.stream.outputWidth:=binary_length _ _
  rw [he] at hl
  have h:=r.stream.output_pos
  simp only [List.length_nil] at hl
  omega

theorem countWord_length_le (r : ResizeTailRequest) : (countWord r).length≤r.word.length := by
  rw [source_shape]
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

theorem streamWord_length_le (r : ResizeTailRequest) : r.stream.word.length≤r.word.length := by
  unfold ResizeTailRequest.word
  rw [List.length_append]
  omega

end NearQuarticWires.StageNativeKidsTail
