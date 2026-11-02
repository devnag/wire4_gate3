import Proof.Quartic.StagePrintTuple.RowFields
import Proof.Quartic.StagePrint.OriginalPipelineFinal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.ThresholdCompiler
open NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator
open StagePrint

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: a first-bank occurrence selects exactly its unchanged
original gate from the actual concatenated occurrence list. -/
theorem RowContext.firstGate_eq (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (h : (r.originalIndex i).val < r.header.call.first.gates.length) :
    callAtoms r.header.call (r.originalIndex i) =
      r.header.call.first.gates[(r.originalIndex i).val] := by
  simp only [callAtoms,Builder.allGates,List.getElem_append_left h]

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: a second-bank occurrence keeps its original relative
position after the exact first-bank offset is removed. -/
theorem RowContext.secondGate_eq (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (h : r.header.call.first.gates.length ≤ (r.originalIndex i).val) :
    callAtoms r.header.call (r.originalIndex i) =
      r.header.call.second.gates[(r.originalIndex i).val-r.header.call.first.gates.length]'(by
        have hi := (r.originalIndex i).isLt
        simp only [Builder.allGates,List.length_append] at hi
        omega) := by
  simp only [callAtoms,Builder.allGates,List.getElem_append_right h]

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: the first-bank row call is the genuine original
call machine at the actual original occurrence and original child. -/
def RowContext.firstPipeline (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (h : (r.originalIndex i).val < r.header.call.first.gates.length)
    (j : Fin (exactChildren (callAtoms r.header.call (r.originalIndex i))).length) :
    OriginalPipelineRequest false where
  source := {
    call := r.header.call
    index := ⟨(r.originalIndex i).val,h⟩
    gate_bits := by
      simpa only [RawBits.originalCircuit,Bool.false_eq_true,ite_false,
        ←r.firstGate_eq i h] using r.gate_bits (r.originalIndex i)
    suffix := [] }
  suffix_empty := rfl
  row := r.originalRow i j
  original_eq := by
    simp only [OriginalRowData.original,RowContext.originalRow,
      RawBits.IndexedCallGateRequest.child,RawBits.originalCircuit,
      Bool.false_eq_true,ite_false]
    change originalChildRequest (Call.B0 r.header.call.n)
      (callAtoms r.header.call (r.originalIndex i)) _ =
      originalChildRequest (Call.B0 r.header.call.n)
        r.header.call.first.gates[(r.originalIndex i).val] _
    congr 1
    exact r.firstGate_eq i h

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: the second-bank row call subtracts only the
actual first-bank occurrence count, preserving the original child. -/
def RowContext.secondPipeline (r : RowContext)
    (i : Fin (17 * (Builder.allGates r.header.call).length))
    (h : r.header.call.first.gates.length ≤ (r.originalIndex i).val)
    (j : Fin (exactChildren (callAtoms r.header.call (r.originalIndex i))).length) :
    OriginalPipelineRequest true where
  source := {
    call := r.header.call
    index := ⟨(r.originalIndex i).val-r.header.call.first.gates.length,by
      change (r.originalIndex i).val-r.header.call.first.gates.length <
        r.header.call.second.gates.length
      have hi := (r.originalIndex i).isLt
      simp only [Builder.allGates,List.length_append] at hi
      omega⟩
    gate_bits := by
      simpa only [RawBits.originalCircuit,ite_true,
        ←r.secondGate_eq i h] using r.gate_bits (r.originalIndex i)
    suffix := [] }
  suffix_empty := rfl
  row := r.originalRow i j
  original_eq := by
    simp only [OriginalRowData.original,RowContext.originalRow,
      RawBits.IndexedCallGateRequest.child,RawBits.originalCircuit,ite_true]
    change originalChildRequest (Call.B0 r.header.call.n)
      (callAtoms r.header.call (r.originalIndex i)) _ =
      originalChildRequest (Call.B0 r.header.call.n)
        (r.header.call.second.gates[(r.originalIndex i).val-r.header.call.first.gates.length]'(by
          have hi := (r.originalIndex i).isLt
          simp only [Builder.allGates,List.length_append] at hi
          omega)) _
    congr 1
    exact r.secondGate_eq i h

end NearQuarticWires.StageTuple
