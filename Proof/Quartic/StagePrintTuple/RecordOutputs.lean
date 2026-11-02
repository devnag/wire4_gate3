import Proof.Quartic.StagePrint.OriginalPipelineFinal
import Proof.Quartic.StagePrint.ChildTuples
import Proof.Quartic.StagePrint.StackPrinter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms.SInt
open StagePrint

/-- `lem:print`, paper/paper.tex: signed dense
field lists are literal nonempty fixed-binary records in row order. -/
def fieldRecords (L : ℕ) (rows : List (List ℤ)) : List (List Bool) :=
  rows.flatten.map (fun z=>binary L (encS z))

/-- `lem:print`, paper/paper.tex: the actual
raw dense-row codec is exactly the concatenation of its field frames. -/
theorem fieldsRecs_eq_records (L : ℕ) (rows : List (List ℤ)) :
    fieldsRecs L rows=(fieldRecords L rows).flatMap frame := by
  simp only [fieldsRecs,fieldRecords,List.flatMap_map]
  rfl

/-- `lem:print`, paper/paper.tex: positive field
width ensures the complete raw record stream has no empty field;
its final blank therefore terminates the physical frame scan. -/
theorem fieldRecords_nonempty (L : ℕ) (hL : 0<L) (rows : List (List ℤ)) :
    ∀ record∈fieldRecords L rows,record≠[] := by
  intro record hr
  obtain ⟨z,_hz,rfl⟩ := List.mem_map.mp hr
  intro he
  have hl := congrArg List.length he
  simp only [SignedSortKey.binary_length,List.length_nil] at hl
  omega

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every actual original-row call emits only its genuine
same-phi native affine fields. -/
def pipelineRecords {second : Bool} (r : OriginalPipelineRequest second) : List (List Bool) :=
  fieldRecords r.row.canonicalPullback.Lout
    [List.ofFn r.row.nativeChild.weight++[r.row.nativeChild.target]]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the real original-row output equals its complete raw
field-frame stream, without a second outer output format. -/
theorem pipeline_output_records {second : Bool} (r : OriginalPipelineRequest second) :
    r.row.canonicalPullback.output=(pipelineRecords r).flatMap frame := by
  rw [r.row.native_output,fieldsRecs_eq_records]
  rfl

/-- `lem:print`, paper/paper.tex: actual row
outputs satisfy the positive-width record condition for physical copying. -/
theorem pipelineRecords_nonempty {second : Bool} (r : OriginalPipelineRequest second) :
    ∀ record∈pipelineRecords r,record≠[] := by
  apply fieldRecords_nonempty
  change 0<r.row.canonicalPullback.Lin+r.row.canonicalPullback.parameters.n+6
  omega

/-- `lem:print`, paper/paper.tex: the actual
original row machine is exposed directly to the raw-record call
controller, with its complete original cold input and unchanged cost. -/
noncomputable def pipelineRecordPrinter (second : Bool) :
    WordFunction (OriginalPipelineRequest second) OriginalPipelineRequest.word
      (fun r=>(pipelineRecords r).flatMap frame) OriginalPipelineRequest.budget :=
  ⟨(originalPipelinePrinter second).program,by
    intro r
    simpa only [←pipeline_output_records r] using (originalPipelinePrinter second).realizes r⟩

/-- `lem:print`, paper/paper.tex: each actual
Cartesian child step is an unframed stream of the same fixed fields. -/
def tupleRecords (r : ChildTupleRequest) : List (List Bool) :=
  fieldRecords r.L (newT r.children r.tuples)

/-- `lem:print`, paper/paper.tex: the checked
Cartesian child printer has exactly the raw-record consumer format. -/
theorem tuple_output_records (r : ChildTupleRequest) :
    r.output=(tupleRecords r).flatMap frame := fieldsRecs_eq_records _ _

/-- `lem:print`, paper/paper.tex: actual
Cartesian child records have positive width even for empty supports. -/
theorem tupleRecords_nonempty (r : ChildTupleRequest) :
    ∀ record∈tupleRecords r,record≠[] := fieldRecords_nonempty r.L r.width_pos _

/-- `lem:print`, paper/paper.tex: the actual
Cartesian printer is consumed unchanged by the raw-record controller. -/
noncomputable def tupleRecordPrinter :
    WordFunction ChildTupleRequest ChildTupleRequest.word
      (fun r=>(tupleRecords r).flatMap frame) (fun r=>2*r.budget+2) :=
  ⟨childTuplePrinter.program,by
    intro r
    simpa only [←tuple_output_records r] using childTuplePrinter.realizes r⟩

/-- `lem:print`, paper/paper.tex: actual signed
stacked equality fields keep the original coefficient and every tuple
in the same literal order as the checked stacking machine. -/
def stackRecords (r : StackRequest) : List (List Bool) :=
  (r.tuples.flatMap (cutL r.s r.coefficient)).map (fun z=>binary (r.W+1) (encS z))

/-- `lem:print`, paper/paper.tex: the actual
signed Stack output is precisely its raw nonempty fixed-field stream. -/
theorem stack_output_records (r : StackRequest) :
    r.output=(stackRecords r).flatMap frame := by
  simp only [StackRequest.output,stackRecords,cutRecs,List.flatMap_map,List.flatMap_assoc]
  rfl

/-- `lem:print`, paper/paper.tex: every actual
signed cut field has positive width, so raw frame scanning terminates
without needing the cut count in advance. -/
theorem stackRecords_nonempty (r : StackRequest) :
    ∀ record∈stackRecords r,record≠[] := by
  intro record hr
  obtain ⟨z,_hz,rfl⟩ := List.mem_map.mp hr
  intro he
  have hl := congrArg List.length he
  simp only [SignedSortKey.binary_length,List.length_nil] at hl
  omega

/-- `lem:print`, paper/paper.tex: the original
signed stack printer is consumed unchanged by the actual raw-record
call controller, with its full existing physical clock. -/
noncomputable def stackRecordPrinter :
    WordFunction StackRequest StackRequest.word
      (fun r=>(stackRecords r).flatMap frame) (fun r=>2*r.budget+2) :=
  ⟨stackPrinter.program,by
    intro r
    simpa only [←stack_output_records r] using stackPrinter.realizes r⟩

end NearQuarticWires.StageTuple
