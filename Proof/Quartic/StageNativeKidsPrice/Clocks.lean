import Proof.Quartic.StageNativeKidsPrice.SourcePrices

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Dispatch
open StageNativeKids StageTuple StagePrint

attribute [local irreducible] RawBits.IndexedCallGateRequest.child compileL

/-- `prop:time`, paper/paper.tex: original
occurrence codecs are charged by their actual bounded binary lengths. -/
theorem index_bits_price : Price SourceCase.scale (fun a => natBitLength a.source.index.val) := by
  have hi := index_price
  have h : Price SourceCase.scale (fun a => a.source.index.val+1) := by source_price
  exact h.mono fun a => natBitLength_le_succ _

/-- `prop:time`, paper/paper.tex: every
original-bank scan and signed source-field conversion has a uniform
price in the literal source, arity and actual child resource. -/
theorem selector_steps_price : Price SourceCase.scale
    (fun a => a.source.steps (ctxOf 4 a.source.source [])) := by
  have hi := index_price
  have hib := index_bits_price
  have hb := bank_bits_price
  have hl := logarithm_price
  have hw := field_price
  have hn := weights_price
  have ht := target_word_price
  have hs := source_word_price
  simp only [RawBits.IndexedCallGateRequest.steps, RawBits.IndexedCallGateRequest.selectSteps,
    RawBits.selectOriginalCost, RawBits.gateFormatterCost, circCost, ctxOf]
  source_price

/-- `prop:time`, paper/paper.tex: the
literal ordinary arithmetic compiler's setup, register operations and
teardown are included in the source selector's polynomial price. -/
theorem arithmetic_price : Price SourceCase.scale (fun a => a.source.arithmeticBudget) := by
  have hl := source_word_price
  have ht := selector_steps_price
  simp only [RawBits.IndexedCallGateRequest.arithmeticBudget, budgetOf, setupCost, KC,
    NearCubicGates.Close.Dispatch.wdOf]
  source_price

/-- `prop:time`, paper/paper.tex: actual
source acquisition includes its physical source framing and handoff. -/
theorem source_price_bound : Price SourceCase.scale (fun a => a.source.sourceBudget) := by
  have hl := source_word_price
  have ht := arithmetic_price
  simp only [RawBits.IndexedCallGateRequest.sourceBudget]
  source_price

/-- `prop:time`, paper/paper.tex: the
concrete original child printer and record framer pay both computation
and the complete literal child stream, with its original cap retained. -/
theorem children_price : Price SourceCase.scale (fun a => a.source.childrenBudget) := by
  have hs := source_price_bound
  have hb := compiler_price
  have ho := output_price
  simp only [RawBits.IndexedCallGateRequest.childrenBudget, childFrameSteps]
  source_price

/-- `prop:time`, paper/paper.tex: the
actual cold record counter scans the real compiled children, including
zero children, rather than receiving a count or a source-price promise. -/
theorem count_steps_price : Price SourceCase.scale
    (fun a => (originalCountRequest a.source.child).steps) := by
  have ho := output_price
  have hc := child_count_price
  have hcb : Price SourceCase.scale
      (fun a => natBitLength (compileL a.source.child.weights a.source.child.target).length) := by
    have h : Price SourceCase.scale
        (fun a => (compileL a.source.child.weights a.source.child.target).length+1) := by source_price
    exact h.mono fun a => natBitLength_le_succ _
  simp only [ChildCountRequest.steps, originalCountRequest_word, originalCountRequest_count]
  source_price

/-- `prop:time`, paper/paper.tex: both
actual original-source count calls have one uniform structural polynomial
price, with all physical composition overhead included. -/
theorem count_price : Price SourceCase.scale (fun a => indexedOriginalCountBudget a.source) := by
  have hs := children_price
  have hc := count_steps_price
  simp only [indexedOriginalCountBudget]
  source_price

end NearQuarticWires.StageNativeKidsPrice
