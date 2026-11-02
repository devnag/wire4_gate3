import Proof.Quartic.StageGreedyCollector.Codec
import Proof.Quartic.StageGreedyEntryBounds.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint

/-- `lem:print`, paper/paper.tex: the real
entry reply contains the reduced signed weak cuts after the actual
per-walk equality split, at the one common native field width. -/
noncomputable def entryOutput {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) : List Bool :=
  frame ((GreedyCollector.walkCuts r.source r.index).flatMap
    (MatrixScoreBatch.cutWord (GreedyCollector.fieldWidth r.source)))

/-- `lem:print` and `prop:time`, paper/paper.tex: one original indexed Terms source is physically
formatted, stacked, split and reduced, with its actual complete budget. -/
abbrev EntryProducer (B1 B2 : ℕ) :=
  (budget : GreedyEntry.Request B1 B2→ℕ) ×
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>(EntryFormat.ofGreedy r).word)
      entryOutput budget

/-- `lem:print`, paper/paper.tex: the common
five-natural header is computed from one actual original entry source;
no header, decoded width or supplied geometry is added to that source. -/
abbrev HeaderProducer (B1 B2 : ℕ) :=
  (budget : GreedyEntry.Request B1 B2→ℕ) ×
    WordFunction (GreedyEntry.Request B1 B2) (fun r=>(EntryFormat.ofGreedy r).word)
      (fun r=>frame (globalHeader r.source)) budget

/-- `prop:time`, paper/paper.tex: each complete
physical entry cost preserves the sharp per-walk exponent twice the
unchanged degree, with a uniform polynomial factor in original arity. -/
def EntryBudgetBound {B1 B2 : ℕ} (budget : GreedyEntry.Request B1 B2→ℕ) : Prop :=
  ∃ K e : ℕ,∀ r,budget r≤K*(r.source.child.call.n+1)^e*
    (r.source.child.selected.1.Uocc^(2*r.degree)+1)

end NearQuarticWires.StageGreedyCollector
