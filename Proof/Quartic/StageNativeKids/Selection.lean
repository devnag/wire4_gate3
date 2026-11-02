import Proof.Quartic.StageNativeKids.RoleBridge
import Proof.Quartic.StagePrintTuple.OriginalCount

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.ThresholdCompiler NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open StageTuple StagePrint

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: a first-bank atom requests its original compiler
directly, even if that compiler produces no child. -/
def firstCountSource (r : NativeKidsRequest)
    (h : (r.toRowContext.originalIndex r.atom).val < r.header.call.first.gates.length) :
    RawBits.IndexedCallGateRequest false where
  call := r.header.call
  index := ⟨(r.toRowContext.originalIndex r.atom).val, h⟩
  gate_bits := by
    simpa only [RawBits.originalCircuit, Bool.false_eq_true, ite_false,
      ←r.toRowContext.firstGate_eq r.atom h] using
      r.gate_bits (r.toRowContext.originalIndex r.atom)
  suffix := []

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: a second-bank atom subtracts the actual first
bank length before requesting the unchanged original compiler. -/
def secondCountSource (r : NativeKidsRequest)
    (h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val) :
    RawBits.IndexedCallGateRequest true where
  call := r.header.call
  index := ⟨(r.toRowContext.originalIndex r.atom).val - r.header.call.first.gates.length, by
    change (r.toRowContext.originalIndex r.atom).val - r.header.call.first.gates.length <
      r.header.call.second.gates.length
    have hi := (r.toRowContext.originalIndex r.atom).isLt
    simp only [Builder.allGates, List.length_append] at hi
    omega⟩
  gate_bits := by
    simpa only [RawBits.originalCircuit, ite_true,
      ←r.toRowContext.secondGate_eq r.atom h] using
      r.gate_bits (r.toRowContext.originalIndex r.atom)
  suffix := []

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: first-bank selection preserves the exact
original gate, including its inclusive threshold and all signed weights. -/
theorem firstCountSource_child (r : NativeKidsRequest)
    (h : (r.toRowContext.originalIndex r.atom).val < r.header.call.first.gates.length) :
    (firstCountSource r h).child = originalChildRequest (Call.B0 r.header.call.n)
      (callAtoms r.header.call (r.toRowContext.originalIndex r.atom))
      (r.gate_bits (r.toRowContext.originalIndex r.atom)) := by
  simp only [firstCountSource, RawBits.IndexedCallGateRequest.child,
    RawBits.originalCircuit, Bool.false_eq_true, ite_false]
  congr 1
  exact (r.toRowContext.firstGate_eq r.atom h).symm

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: second-bank selection preserves the same
original gate after only the actual occurrence offset is removed. -/
theorem secondCountSource_child (r : NativeKidsRequest)
    (h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val) :
    (secondCountSource r h).child = originalChildRequest (Call.B0 r.header.call.n)
      (callAtoms r.header.call (r.toRowContext.originalIndex r.atom))
      (r.gate_bits (r.toRowContext.originalIndex r.atom)) := by
  simp only [secondCountSource, RawBits.IndexedCallGateRequest.child,
    RawBits.originalCircuit, ite_true]
  congr 1
  exact (r.toRowContext.secondGate_eq r.atom h).symm

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the actual first-bank record counter computes
the native child-pool length, also when that length is zero. -/
theorem firstCountSource_count (r : NativeKidsRequest)
    (h : (r.toRowContext.originalIndex r.atom).val < r.header.call.first.gates.length) :
    (compileL (firstCountSource r h).child.weights (firstCountSource r h).child.target).length =
      (r.toRowContext.nativeKids r.atom).length := by
  rw [firstCountSource_child, originalChildRequest_children]
  simp only [List.length_map, r.toRowContext.nativeKids_length]

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: the actual second-bank record counter computes
the native pool length, with duplicate occurrences retaining their indices. -/
theorem secondCountSource_count (r : NativeKidsRequest)
    (h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val) :
    (compileL (secondCountSource r h).child.weights (secondCountSource r h).child.target).length =
      (r.toRowContext.nativeKids r.atom).length := by
  rw [secondCountSource_child, originalChildRequest_children]
  simp only [List.length_map, r.toRowContext.nativeKids_length]

end NearQuarticWires.StageNativeKids
