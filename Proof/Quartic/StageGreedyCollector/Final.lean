import Proof.Quartic.StageGreedyCollector.Selected
import Proof.Quartic.StageGreedyEntry.Final

/-!
# The compiled walk collector

Paper: `lem:print` and `prop:time`, paper/paper.tex.

The collector computes the common native header and concatenates the
reduced weak rows of all compiled walk entries in their original order.
Its ordinary machine and selected running-time bound use the same budget.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open StagePrint

/-- `lem:print`, paper/paper.tex: the ordinary machine
from the compiled walk stream to the framed common header and weak rows. -/
noncomputable def collectorProducer (B1 B2 : ℕ) : GreedyCollector.Producer B1 B2 :=
  producer_of_header_entry (StageGreedyEntry.headerProducer B1 B2)
    (StageGreedyEntry.entryProducer B1 B2)

/-- `prop:time`, paper/paper.tex: the actual collector
budget is bounded by the number of columns times a polynomial in the arity. -/
theorem collectorProducer_selected (B1 B2 : ℕ) :
    ∃ K e : ℕ, ∀ r : Greedy.PrintRequest B1 B2, (collectorProducer B1 B2).1 r ≤
      K * 2 ^ (r.child.call.n - r.child.selected.1.k) * (r.child.call.n + 1) ^ e :=
  producer_budget_selected (StageGreedyEntry.headerProducer B1 B2)
    (StageGreedyEntry.entryProducer B1 B2)
    (StageGreedyEntry.headerProducer_bound B1 B2)
    (StageGreedyEntry.entryProducer_bound B1 B2)

end NearQuarticWires.StageGreedyCollector
