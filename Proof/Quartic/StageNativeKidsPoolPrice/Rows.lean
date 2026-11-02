import Proof.Quartic.StageNativeKidsPoolPrice.Resources

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPoolPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageNativeKids StageNativeKidsPrice StageNativeKidsPool StageTuple StagePrint

theorem pipeline_input_length (source header : List Bool) (j : ℕ) :
    (pipelineInputWord source (List.replicate j true) header).length=
      4*(source.length+j+header.length)+17 := by
  simp only [pipelineInputWord,Top.loadRec,List.length_append,frame_length,
    List.length_replicate,List.length_nil]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual original-child row
input has a structural price at the same original source scale. -/
theorem row_input_price : Price RowCase.scale (fun b=>b.pipeline.word.length) := by
  have hs : Price RowCase.scale (fun b=>(actualFamily b.toSourceCase).source.length) :=
    source_price.comp RowCase.toSourceCase
  have hh : Price RowCase.scale (fun b=>(actualFamily b.toSourceCase).header.length) :=
    header_price.comp RowCase.toSourceCase
  have hi:=index_price
  have h : Price RowCase.scale (fun b=>4*((actualFamily b.toSourceCase).source.length+
      b.childIndex.val+(actualFamily b.toSourceCase).header.length)+17) := by
    price_with row_scale_pos
  apply h.mono
  intro b
  have he:=row_input b.toSourceCase b.childIndex
  change b.pipeline.word=_ at he
  rw [he,pipeline_input_length]
  exact le_rfl

/-- `prop:time`, paper/paper.tex: the
actual per-occurrence clock includes real input formatting, the
concrete original pipeline budget, copying, cleanup and progression. -/
theorem occurrence_price : Price RowCase.scale (fun b=>
    occurrenceCost (actualFamily b.toSourceCase).source (actualFamily b.toSourceCase).header
      b.childIndex.val b.pipeline.word.length b.pipeline.budget) := by
  have hs : Price RowCase.scale (fun b=>(actualFamily b.toSourceCase).source.length) :=
    source_price.comp RowCase.toSourceCase
  have hh : Price RowCase.scale (fun b=>(actualFamily b.toSourceCase).header.length) :=
    header_price.comp RowCase.toSourceCase
  have hi:=index_price
  have hw:=row_input_price
  have hb:=StageNativeKidsPrice.row_price
  simp only [occurrenceCost,pipelineCounterInputCost,callRecordsCost,frame_length]
  price_with row_scale_pos

end NearQuarticWires.StageNativeKidsPoolPrice
