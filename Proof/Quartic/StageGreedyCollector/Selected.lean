import Proof.Quartic.StageGreedyCollector.Budget
import Proof.Quartic.StageGreedyCollector.ContextLength
import Proof.Quartic.StageGreedyCollector.EntrySelected

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open StagePrint

/-- `prop:time`, paper/paper.tex: the
SAME full physical collector budget satisfies the selected column
bound. The actual finite context, one header call, all original
per-entry calls, every byte copy and final weak-row concatenation are
charged without multiplying the source length by a census square. -/
theorem producer_budget_selected {B1 B2 : ℕ} (H : HeaderProducer B1 B2) (E : EntryProducer B1 B2)
    (hH : EntryBudgetBound H.1) (hE : EntryBudgetBound E.1) :
    ∃K e : ℕ,∀r : Greedy.PrintRequest B1 B2,(producer_of_header_entry H E).1 r≤
      K*2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e := by
  have hc : SelectedBudget (StageGreedyContext.contextProducer B1 B2).1 :=
    context_budget_selected (StageGreedyContext.contextProducer_bound B1 B2)
  have hh:=first_budget_selected hH
  have hr:=repeated_context_selected B1 B2
  have he:=repeated_entry_budget_selected E hE
  have hn:=walk_count_selected B1 B2
  have hs:=(((((hc.add hh).add hr).add he).add hn).add (SelectedBudget.const 1)).scale (10^15)
  apply hs.mono
  intro r
  calc
    _≤10^15*((StageGreedyContext.contextProducer B1 B2).1 r+
      H.1 (firstActualEntry r)+(entryCalls r).length*((contextWord r).length+entryMaximum E r+2)+1):=
        producerBudget_linear H E r
    _=_:=by ring

end NearQuarticWires.StageGreedyCollector
