import Proof.Quartic.StagePrintTuple.RowSource
import Proof.Quartic.StagePrintTuple.PipelineInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the exact
canonical affine row header depends on the original occurrence role
and walk, but never on which original child is selected. -/
def RowContext.rowHeader (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) : List Bool :=
  (StagePrint.Header.baseHeaderValues r.header).flatMap natWord ++
    natWord (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
      (StagePrint.Header.roleLeftSlot (r.role i))).val ++
    natWord (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
      (StagePrint.Header.roleRightSlot (r.role i))).val ++
    [StagePrint.Header.leftCornerCode (finProdFinEquiv.symm i).1.val,
      StagePrint.Header.rightCornerCode (finProdFinEquiv.symm i).1.val,true]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the nine actual canonical affine scalars are precisely
the common retained prefix and the two physically selected walk vertices. -/
theorem RowContext.originalRow_fields (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.originalRow i j).canonicalPullback.fields=
      StagePrint.Header.baseHeaderValues r.header ++
      [(StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
        (StagePrint.Header.roleLeftSlot (r.role i))).val,
       (StagePrint.indexedWalk r.header.prepared.seedParameters.N r.walkCode
        (StagePrint.Header.roleRightSlot (r.role i))).val] := by
  simp only [StagePullback.RowRequest.fields]
  rw [r.originalRow_Lin_eq,r.originalRow_Lout_eq]
  simp only [StagePrint.Header.baseHeaderValues,RowContext.nativeFieldWidth,
    RowContext.inputFieldWidth]
  simp only [RowContext.originalRow,StagePrint.OriginalRowData.canonicalPullback,
    StagePrint.OriginalRowData.pullback,Builder.star,Cells.ParameterRules.star_b,
    Cells.ParameterRules.star_s]
  rfl

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every actual original child consumes exactly the same
retained role header, preserving all three literal corner flags. -/
theorem RowContext.originalRow_header (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.originalRow i j).header (r.originalRow i j).fields_fit=r.rowHeader i := by
  change (r.originalRow i j).canonicalPullback.fields.flatMap natWord ++ _ = _
  rw [r.originalRow_fields]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    RowContext.originalRow,RowContext.rowHeader,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the physically
formatted three-field request matches the actual first-bank row call,
including the original compiler index and child-independent header. -/
theorem RowContext.firstPipeline_word (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (h : (r.originalIndex i).val<r.header.call.first.gates.length)
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.firstPipeline i h j).word=pipelineInputWord
      (natWord (r.originalIndex i).val++NearCubicGates.Close.Interfaces.callWord r.header.call)
      (List.replicate j.val true) (r.rowHeader i) := by
  simp only [StagePrint.OriginalPipelineRequest.word,RowContext.firstPipeline,
    StagePrint.RawBits.IndexedCallGateRequest.source,List.append_nil,
    StagePrint.OriginalRowData.compilerIndex,r.originalRow_header]
  rfl

/-- `lem:print`, paper/paper.tex: the same
actual cold codec is used in the second bank after subtracting only its
real first-bank offset, with original child order unchanged. -/
theorem RowContext.secondPipeline_word (r : RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length))
    (h : r.header.call.first.gates.length≤(r.originalIndex i).val)
    (j : Fin (exactChildren (StagePrint.callAtoms r.header.call (r.originalIndex i))).length) :
    (r.secondPipeline i h j).word=pipelineInputWord
      (natWord ((r.originalIndex i).val-r.header.call.first.gates.length)++
        NearCubicGates.Close.Interfaces.callWord r.header.call)
      (List.replicate j.val true) (r.rowHeader i) := by
  simp only [StagePrint.OriginalPipelineRequest.word,RowContext.secondPipeline,
    StagePrint.RawBits.IndexedCallGateRequest.source,List.append_nil,
    StagePrint.OriginalRowData.compilerIndex,r.originalRow_header]
  rfl

end NearQuarticWires.StageTuple
