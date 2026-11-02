import Proof.Quartic.StagePrint.RecordSelect
import Proof.MachineModel.OrdinaryBoundedCounter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

/-- `lem:print`, paper/paper.tex: fixed-width original child records retain their literal bits. -/
structure BitRecordSelectRequest where
  L : ℕ
  records : List (List Bool)
  index : Fin records.length
  width_pos : 1≤L
  record_length : ∀ row∈records,row.length=L

/-- `lem:print`, paper/paper.tex: integer interpretation only identifies the unchanged physical binary records. -/
def BitRecordSelectRequest.lower (r : BitRecordSelectRequest) : RecordSelectRequest where
  L:=r.L
  values:=r.records.map value
  index:=⟨r.index.val,by simpa using r.index.isLt⟩
  width_pos:=r.width_pos

/-- `lem:print`, paper/paper.tex: interpreting and reprinting a record does not truncate or otherwise alter its bits. -/
theorem bitRecord_binary (r : BitRecordSelectRequest) (row : List Bool) (hr : row∈r.records) :
    binary r.L (value row)=row := by
  rw [←r.record_length row hr]
  exact BoundedCounter.binary_of_value row

/-- `lem:print`, paper/paper.tex: the source contains actual framed records and an explicit selection index. -/
def BitRecordSelectRequest.word (r : BitRecordSelectRequest) : List Bool :=
  Top.loadRec (recStream r.records) (List.replicate r.index.val true) [] [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: no conversion of a child record is required before physical selection. -/
theorem bitRecord_word (r : BitRecordSelectRequest) : r.lower.word=r.word := by
  unfold RecordSelectRequest.word BitRecordSelectRequest.lower BitRecordSelectRequest.word
  congr 2
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_map]
    exact bitRecord_binary r _ (List.getElem_mem hj)

/-- `lem:print`, paper/paper.tex: the selected native record equals the original bit string exactly. -/
theorem bitRecord_output (r : BitRecordSelectRequest) :
    binary r.lower.L r.lower.values[r.lower.index.val]=r.records[r.index.val] := by
  change binary r.L (r.records.map value)[r.index.val]=_
  rw [List.getElem_map]
  exact bitRecord_binary r _ (List.getElem_mem r.index.isLt)

/-- `lem:print`, paper/paper.tex: a cold fixed-width binary source yields exactly its selected original child record. -/
noncomputable def bitRecordSelector :
    WordFunction BitRecordSelectRequest BitRecordSelectRequest.word
      (fun r=>frame r.records[r.index.val]) (fun r=>2*r.lower.budget+2) :=
  ⟨recordSelector.program,by
    intro r
    simpa only [bitRecord_word,bitRecord_output] using recordSelector.realizes r.lower⟩

end NearQuarticWires.StagePrint
