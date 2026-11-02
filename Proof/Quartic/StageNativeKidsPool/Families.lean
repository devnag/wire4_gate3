import Proof.Quartic.StageNativeKids.PoolRequest
import Proof.Quartic.StageNativeKidsPrice.Final
import Proof.Quartic.StagePrintTuple.RecordOutputs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine
open StageNativeKids StageNativeKidsPrice StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: the actual
bank case has exactly its original finite exact-child index set. -/
abbrev Children (a : SourceCase) :=
  Fin (exactChildren (callAtoms a.request.header.call
    (a.request.toRowContext.originalIndex a.request.atom))).length

/-- `lem:print`, paper/paper.tex: the
actual loop index alone chooses one unchanged original pipeline call. -/
def rowRequest (a : SourceCase) (j : Children a) : OriginalPipelineRequest a.second :=
  (RowCase.mk a j).pipeline

/-- `lem:print`, paper/paper.tex: the
counter's actual original compiler counts precisely the row loop. -/
theorem source_count (a : SourceCase) :
    (compileL a.source.child.weights a.source.child.target).length =
      (a.request.toRowContext.nativeKids a.request.atom).length := by
  rcases a with ⟨r,b,h⟩
  cases b
  · exact firstCountSource_count r h
  · exact secondCountSource_count r h

/-- `lem:print`, paper/paper.tex: every
computed row index uses the retained original source and common affine
header, with the exact existing nested unary-index codec. -/
theorem row_input (a : SourceCase) (j : Children a) :
    (rowRequest a j).word = pipelineInputWord a.source.source (List.replicate j.val true)
      (a.request.toRowContext.rowHeader a.request.atom) := by
  rcases a with ⟨r,b,h⟩
  cases b
  · simpa only [rowRequest,RowCase.pipeline,SourceCase.source,firstCountSource,
      RawBits.IndexedCallGateRequest.source,List.append_nil] using
      r.toRowContext.firstPipeline_word r.atom h j
  · simpa only [rowRequest,RowCase.pipeline,SourceCase.source,secondCountSource,
      RawBits.IndexedCallGateRequest.source,List.append_nil] using
      r.toRowContext.secondPipeline_word r.atom h j

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every real row call produces exactly the
corresponding native row before any target-width resize. -/
theorem row_output (a : SourceCase) (j : Children a) :
    (pipelineRecords (rowRequest a j)).flatMap frame =
      fieldsRecs a.request.toRowContext.nativeFieldWidth
        [List.ofFn (a.request.toRowContext.originalRow a.request.atom j).nativeChild.weight ++
          [(a.request.toRowContext.originalRow a.request.atom j).nativeChild.target]] := by
  rw [←pipeline_output_records]
  rcases a with ⟨r,b,h⟩
  cases b <;> exact r.toRowContext.originalRow_output r.atom j

/-- `lem:print`, paper/paper.tex: the
actual increasing child loop concatenates precisely the original-order
native pool, including the empty-child case. -/
theorem rows_output (a : SourceCase) :
    (List.ofFn fun j : Children a=>(pipelineRecords (rowRequest a j)).flatMap frame).flatten =
      fieldsRecs a.request.toRowContext.nativeFieldWidth
        (a.request.toRowContext.nativeKids a.request.atom) := by
  simp_rw [row_output]
  simp only [fieldsRecs,RowContext.nativeKids,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.flatMap_def,List.map_flatten,
    List.map_ofFn,List.flatten_flatten,List.map_map,Function.comp_def]

end NearQuarticWires.StageNativeKidsPool
