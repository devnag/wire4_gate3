import Proof.Quartic.StageGreedyEntry.TupleLedger
import Proof.Quartic.StageTupleOuter.Sharp

/-!
# The cold tuple printer's clock at actual entries

Paper: `lem:print`, `sec:params` and `prop:time`, paper/paper.tex.

The sharp request-level ledger `StageTupleOuter.budget_sharp`, instantiated at the original child bound
`mc = childCap`, gives the selected per-entry bound (`tuple_ebb_of_sharp`): the structural census magnitude is
polynomial in the original arity (`structural_arity`) and every original child pool has at most `childCap`
members (`nativeKids_le_childCap`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint StageGreedyCollector StageTuple

variable {B1 B2 : ℕ}

theorem childCap_pos (r : GreedyEntry.Request B1 B2) : 1 ≤ r.source.child.selected.1.childCap := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hn:=hs.n_pos
  rw [hs.childCap_eq]
  unfold Cells.childCap
  exact Nat.mul_pos hn (by omega)

/-- `prop:time`, paper/paper.tex: the cold tuple printer meets the selected per-entry
bound at actual entries. -/
theorem tuple_ebb_of_sharp (B1 B2 : ℕ) {B : StageNativeKids.NativeKidsRequest → ℕ}
    {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B} {nativePrice : NativeStagePrice B}
    (M : TermStageMachine native nativePrice) {Bs : TermCutRequest → ℕ} (hBs : TupleSetupCost Bs) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>StageTupleOuter.termCutBudget M Bs r.termRequest) := by
  obtain ⟨C,E,_,_,h⟩:=StageTupleOuter.budget_sharp M hBs
  obtain ⟨K,e,hK⟩:=structural_arity B1 B2
  exact tuple_ebb C E (fun t mc=>t.censusMagnitude mc)
    (fun t mc=>1 ≤ mc ∧ ∀i,(t.toRowContext.nativeKids i).length ≤ mc)
    (fun t mc h'=>h t mc h'.1 h'.2)
    (fun r=>⟨childCap_pos r,nativeKids_le_childCap r⟩)
    ⟨K,e,fun r=>hK r⟩

end NearQuarticWires.StageGreedyEntry
