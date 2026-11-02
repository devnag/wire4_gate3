import Proof.Quartic.StagePrint.OriginalRowSelect
import Proof.Quartic.StagePrint.CallFieldBounds
import Proof.Quartic.StagePrint.RowSelectorInput
import Proof.Quartic.StagePullback.RowRequest

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

/-- `imp:pullback` and `lem:print`, paper/paper.tex: one original disjoint child is selected before its actual walk-corner metadata are applied. -/
structure OriginalRowData where
  parameters : StarParams
  gate : NormalizedThresholdGate parameters.n
  gate_bits : GateBits (Call.B0 parameters.n) gate
  index : Fin (exactChildren gate).length
  translation : parameters.Translation
  left : Fin (2 ^ NearCubicWires.WireExponent3_5.SeedFix.callKh parameters)
  right : Fin (2 ^ NearCubicWires.WireExponent3_5.SeedFix.callKh parameters)
  useLeft : Bool
  useRight : Bool
  transpose : Bool

/-- `lem:print`, paper/paper.tex: the original compiler request is independent of every corner flag. -/
def OriginalRowData.original (r : OriginalRowData) : OriginalChildRequest :=
  originalChildRequest (Call.B0 r.parameters.n) r.gate r.gate_bits

/-- `lem:print`, paper/paper.tex: the selected exact equation is an actual original child. -/
def OriginalRowData.child (r : OriginalRowData) : ExactEquation r.parameters.n :=
  (exactChildren r.gate)[r.index.val]

/-- `lem:print`, paper/paper.tex: original child occurrence order is unchanged by serialization. -/
def OriginalRowData.compilerIndex (r : OriginalRowData) :
    Fin (compileL r.original.weights r.original.target).length :=
  ⟨r.index.val,by
    rw [show compileL r.original.weights r.original.target=(exactChildren r.gate).map kidL from
      originalChildRequest_children _ _ _]
    simpa using r.index.isLt⟩

/-- `lem:print`, paper/paper.tex: the actual compiler-selected integer row equals the original child's dense weights and target. -/
theorem OriginalRowData.compilerRow (r : OriginalRowData) :
    (compileL r.original.weights r.original.target)[r.compilerIndex.val]=kidL r.child := by
  rw [←List.getD_eq_getElem _ [] r.compilerIndex.isLt]
  change (compileL r.original.weights r.original.target).getD r.index.val []=kidL r.child
  rw [show compileL r.original.weights r.original.target=(exactChildren r.gate).map kidL from
    originalChildRequest_children _ _ _]
  rw [List.getD_eq_getElem _ [] (by simpa using r.index.isLt)]
  simp [child]

/-- `imp:pullback`, paper/paper.tex: the original child is placed in the canonical affine request without changing its signed fields. -/
def OriginalRowData.pullback (r : OriginalRowData)
    (hfit : ∀z∈kidL r.child,SInt.encS z<2^(r.original.W+1)) : StagePullback.RowRequest where
  parameters:=r.parameters
  translation:=r.translation
  left:=r.left
  right:=r.right
  useLeft:=r.useLeft
  useRight:=r.useRight
  transpose:=r.transpose
  Lin:=r.original.W+1
  Lin_pos:=by omega
  Lin_le:=call_original_field_width r.gate r.gate_bits
  child:=Cells.childGate r.child
  weightsFit:=by
    intro i
    apply hfit
    simp [kidL,Cells.childGate,List.mem_ofFn]
  targetFits:=by
    apply hfit
    simp [kidL,Cells.childGate]

/-- `lem:print`, paper/paper.tex: the original-row selector's actual cold input is exactly the formatter output. -/
theorem OriginalRowData.selectorInput (r : OriginalRowData) :
    originalRowInput r.original.output (List.replicate r.compilerIndex.val true)=
      (originalRowRequest r.original r.compilerIndex).word := by
  rw [originalRowRequest_word]
  rfl

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the selected physical row bytes are precisely the unframed body consumed by the actual affine row printer. -/
theorem OriginalRowData.pullbackBody (r : OriginalRowData)
    (hfit : ∀z∈kidL r.child,SInt.encS z<2^(r.original.W+1)) :
    (r.pullback hfit).body=recBits r.original.W
      (compileL r.original.weights r.original.target)[r.compilerIndex.val] := by
  rw [r.compilerRow]
  rw [StagePullback.RowRequest.body_recBits]
  rfl

/-- `imp:pullback`, paper/paper.tex: the prefix is the exact nine canonical scalar fields and three physical flags, with no supplied side or flip arrays. -/
def OriginalRowData.header (r : OriginalRowData)
    (hfit : ∀z∈kidL r.child,SInt.encS z<2^(r.original.W+1)) : List Bool :=
  (r.pullback hfit).fields.flatMap NearCubicWires.RepairRepresentation.natWord++
    [r.useLeft,r.useRight,r.transpose]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: physically joining the actual header and selected original row produces the exact affine-printer input. -/
theorem OriginalRowData.pullbackWord (r : OriginalRowData)
    (hfit : ∀z∈kidL r.child,SInt.encS z<2^(r.original.W+1)) :
    r.header hfit++recBits r.original.W
      (compileL r.original.weights r.original.target)[r.compilerIndex.val]=
      (r.pullback hfit).word := by
  rw [←r.pullbackBody hfit]
  rfl

end NearQuarticWires.StagePrint
