import Proof.Quartic.StageGreedyCollector.Entry
import Proof.Quartic.StagePrintContext.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation

/-- `lem:print`, paper/paper.tex: the only
repeated source prefix contains the original arity and the one actual
common affine context computed from the preparation. -/
def contextWord {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  natWord r.child.call.n++StagePrint.Context.word (StagePrint.GreedyCollector.prepared r)

/-- Step 3 and `lem:print`, paper/paper.tex: one framed context is followed by the original binary
walk count and every unchanged indexed compiled entry. -/
noncomputable def contextualWord {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  frame (contextWord r)++natWord (r.child.cellCall.seed.N^8)++
    (List.ofFn (StagePrint.TermsCarrier.entryWord r)).flatten

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical context construction reads the actual
carrier, computes one common context and copies each source entry once. -/
abbrev ContextProducer (B1 B2 : ℕ) :=
  (budget : Greedy.PrintRequest B1 B2→ℕ) ×
    WordFunction (Greedy.PrintRequest B1 B2) StagePrint.TermsCarrier.word
      (fun r=>frame (contextualWord r)) budget

/-- `prop:time`, paper/paper.tex: context
construction is linear in the actual carrier length, with a fixed
polynomial factor in the original arity. -/
def ContextBudgetBound {B1 B2 : ℕ} (budget : Greedy.PrintRequest B1 B2→ℕ) : Prop :=
  ∃ K e : ℕ,∀ r,budget r≤K*(r.child.call.n+1)^e*((StagePrint.TermsCarrier.word r).length+1)

end NearQuarticWires.StageGreedyCollector
