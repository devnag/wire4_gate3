import Proof.Quartic.StagePrint.EntryReaderCost
import Proof.Quartic.StageEntryAllocation.Allocation
import Proof.Quartic.StageGreedyEntryBounds.Polynomial
import Proof.Quartic.StageGreedyCollector.PerEntryTarget

/-!
# The shared formatter on one actual compiled walk entry

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`formatter B1 B2` is the closed ordinary EntryFormat formatter under the fixed original-arity
allocation, read on the literal entry bytes `(EntryFormat.ofGreedy r).word` and writing
`frame r.termRequest.word`. `formatter_bound` is the selected per-entry clock: the formatter is
linear in the literal word, and the word has at most `Uocc^(2D)` Terms records of polynomial height.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StagePrint

/-- `lem:print`, paper/paper.tex: the fixed coefficient of the
original-arity sizing polynomial for actual entries. -/
noncomputable def sizingC (B1 B2 : ℕ) : ℕ :=
  (StageGreedyEntryBounds.sizingMagnitude_ofGreedy_polynomial B1 B2).choose

/-- `lem:print`, paper/paper.tex: the fixed exponent of the
original-arity sizing polynomial for actual entries. -/
noncomputable def sizingE (B1 B2 : ℕ) : ℕ :=
  (StageGreedyEntryBounds.sizingMagnitude_ofGreedy_polynomial B1 B2).choose_spec.choose

theorem sizing_spec {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (EntryFormat.ofGreedy r).sizingMagnitude ≤ sizingC B1 B2*(r.source.child.call.n+1)^sizingE B1 B2 :=
  (StageGreedyEntryBounds.sizingMagnitude_ofGreedy_polynomial B1 B2).choose_spec.choose_spec r

/-- `lem:print`, paper/paper.tex: the actual entry request with
its proved sizing bound; the runtime word is unchanged. -/
noncomputable def bounded {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    EntryFormat.BoundedRequest (sizingC B1 B2) (sizingE B1 B2) true where
  toRequest:=EntryFormat.ofGreedy r
  size_bound:=sizing_spec r

/-- `prop:time`, paper/paper.tex: the formatter's clock. -/
noncomputable def formatterBudget (B1 B2 : ℕ) (r : GreedyEntry.Request B1 B2) : ℕ :=
  EntryFormat.allocatedBudget (StageEntryAllocation.allocation (sizingC B1 B2) (sizingE B1 B2) true)
    (bounded r)

/-- `lem:print`, paper/paper.tex: the closed shared formatter
maps the literal entry bytes to the framed actual tuple request. -/
noncomputable def formatter (B1 B2 : ℕ) :
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>(EntryFormat.ofGreedy r).word)
      (fun r=>frame r.termRequest.word) (formatterBudget B1 B2) where
  program:=(EntryFormat.formatterWithAllocation
    (StageEntryAllocation.allocation (sizingC B1 B2) (sizingE B1 B2) true)).program
  realizes:=fun r=>(EntryFormat.formatterWithAllocation
    (StageEntryAllocation.allocation (sizingC B1 B2) (sizingE B1 B2) true)).realizes (bounded r)

end NearQuarticWires.StageGreedyEntry
