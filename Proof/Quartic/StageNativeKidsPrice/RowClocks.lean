import Proof.Quartic.StageNativeKidsPrice.Rows
import Proof.Quartic.StageNativeKidsPrice.Clocks

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Dispatch
open NearCubicGates.Close.WordPrograms
open StageNativeKids StageTuple StagePrint

attribute [local irreducible] RowCase.pipeline SourceCase.source
  RawBits.IndexedCallGateRequest.child compileL OriginalChildRequest.output
  OriginalPipelineRequest.rowBody OriginalPipelineRequest.pullBudget
  OriginalPipelineRequest.selectBudget

/-- `prop:time`, paper/paper.tex: the
eleven-field selector loader costs its actual fixed-width record stream
and its actual unary original-child index. -/
theorem selector_loadCost (r : RecordSelectRequest) :
    r.loadCost = 12*(r.values.length*(2*r.L+1)+r.index.val)+105 := by
  have hr : (recStream (r.values.map (SignedSortKey.binary r.L))).length =
      r.values.length*(2*r.L+1)+1 := by
    rw [recStream_length r.L _ (by
      intro row hrow
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hrow
      exact SignedSortKey.binary_length _ _), List.length_map]
  simp only [RecordSelectRequest.loadCost, Top.loadCost, Top.loadRec, Top.loadChainCost,
    List.length_append, RepairOrdinary.frame_length, List.length_nil, List.length_replicate]
  rw [hr]
  ring

/-- `prop:time`, paper/paper.tex: the
original row pipeline's cold loader pays its source, original child
index and actual affine header, each in its physical nested frame. -/
theorem pipeline_loadCost {second : Bool} (r : OriginalPipelineRequest second) :
    r.loadCost = 24*(r.source.source.length+r.row.compilerIndex.val+
      (r.row.header r.row.fields_fit).length)+129 := by
  simp only [OriginalPipelineRequest.loadCost, Top.loadCost, Top.loadRec, Top.loadChainCost,
    List.length_append, RepairOrdinary.frame_length, List.length_nil, List.length_replicate]
  ring

/-- `prop:time`, paper/paper.tex: the
concrete row selector's loader and complete indexed record scan have
a uniform structural polynomial price. -/
theorem row_selection_price : Price RowCase.scale (fun a => a.pipeline.selectBudget) := by
  have hw := row_field_price
  have hn := row_weights_price
  have hc := row_count_price
  have hi := row_index_price
  simp only [OriginalPipelineRequest.selectBudget, RecordSelectRequest.budget,
    selector_loadCost, BitRecordSelectRequest.lower, originalRowRequest, List.length_map]
  price_with row_scale_pos

/-- `prop:time`, paper/paper.tex: the
actual same-center affine pullback clock has a fixed original-arity
polynomial price, including all signed arithmetic and serialization. -/
theorem row_pullback_price : Price RowCase.scale (fun a => a.pipeline.pullBudget) := by
  have hn : Price RowCase.scale (fun a => a.request.header.call.n) :=
    arity_price.comp RowCase.toSourceCase
  have h : Price RowCase.scale (fun a =>
      10^12*(NearCubicGates.Close.Cells.TSK StagePullback.coordinateCallee+5000)^2*
        (a.request.header.call.n+2)^11) := by price_with row_scale_pos
  apply h.mono
  intro a
  simp only [OriginalPipelineRequest.pullBudget]
  simpa only [row_dimension] using StagePullback.rowCost_polynomial a.pipeline.row.canonicalPullback

/-- `prop:time`, paper/paper.tex: the
complete original pipeline includes its cold loader, all three actual
callees and every physical copy, rewind, frame and sequence transition. -/
theorem row_price : Price RowCase.scale (fun a => a.pipeline.budget) := by
  have hs : Price RowCase.scale (fun a => a.pipeline.source.source.length) := by
    have h : Price RowCase.scale (fun a => a.toSourceCase.source.source.length) :=
      source_word_price.comp RowCase.toSourceCase
    exact h.mono fun a => (congrArg (fun s => s.source.length) (row_source a)).le
  have hc : Price RowCase.scale (fun a => a.pipeline.source.childrenBudget) := by
    have h : Price RowCase.scale (fun a => a.toSourceCase.source.childrenBudget) :=
      children_price.comp RowCase.toSourceCase
    exact h.mono fun a => (congrArg (fun s => s.childrenBudget) (row_source a)).le
  have ho : Price RowCase.scale (fun a => a.pipeline.row.original.output.length) := by
    have h : Price RowCase.scale (fun a => a.toSourceCase.source.child.output.length) :=
      output_price.comp RowCase.toSourceCase
    exact h.mono fun a => (congrArg (fun r => r.output.length) (row_original a)).le
  have hi := row_index_price
  have hh := row_header_price
  have hb := row_body_price
  have hselect := row_selection_price
  have hpull := row_pullback_price
  simp only [OriginalPipelineRequest.budget, OriginalPipelineRequest.clock,
    pipeline_loadCost, OriginalPipelineRequest.selectorFormatCost,
    OriginalPipelineRequest.pullFormatCost, originalRowInputCost, pullbackInputCost,
    List.length_replicate]
  price_with row_scale_pos

end NearQuarticWires.StageNativeKidsPrice
