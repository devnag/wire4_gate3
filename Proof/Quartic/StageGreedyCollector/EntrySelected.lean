import Proof.Quartic.StageGreedyCollector.CostArithmetic
import Proof.Quartic.StageGreedyCollector.EntryBatch

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open StagePrint

/-- `prop:time`, paper/paper.tex: one
actual original first-entry call uses at most the selected column
reserve, retaining its sharp degree and supplied complete physical budget. -/
theorem first_budget_selected {B1 B2 : ℕ} {budget : GreedyEntry.Request B1 B2→ℕ}
    (h : EntryBudgetBound budget) : SelectedBudget (fun r=>budget (firstActualEntry r)) := by
  obtain ⟨K,e,hK⟩:=h
  refine ⟨2*K,e,fun r=>?_⟩
  have hn:=StageLiftSourceCost.walkCount_pos r
  have hs:=entry_squared_reserve_add (firstActualEntry r)
  have hu : r.child.selected.1.Uocc^(2*(firstActualEntry r).degree)+1≤
      2*2^(r.child.call.n-r.child.selected.1.k) :=
    (Nat.le_mul_of_pos_left _ hn).trans hs
  calc
    _≤K*(r.child.call.n+1)^e*(r.child.selected.1.Uocc^(2*(firstActualEntry r).degree)+1):=hK _
    _≤K*(r.child.call.n+1)^e*(2*2^(r.child.call.n-r.child.selected.1.k)):=
      Nat.mul_le_mul_left _ hu
    _=_:=by ring

/-- `prop:time`, paper/paper.tex: each
actual original call has the same selected degree and census, so the
maximum genuine call budget obeys that common sharp bound. -/
theorem entryMaximum_uniform {B1 B2 : ℕ} (E : EntryProducer B1 B2) (K e : ℕ)
    (hK : ∀r,E.1 r≤K*(r.source.child.call.n+1)^e*
      (r.source.child.selected.1.Uocc^(2*r.degree)+1)) (r : Greedy.PrintRequest B1 B2) :
    entryMaximum E r≤K*(r.child.call.n+1)^e*
      (r.child.selected.1.Uocc^(2*(firstActualEntry r).degree)+1) := by
  unfold entryMaximum
  apply List.max_le_of_forall_le
  intro v hv
  obtain ⟨entry,he,rfl⟩:=List.mem_map.mp hv
  rw [entryCalls] at he
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
  exact hK ⟨r,i⟩

/-- `prop:time`, paper/paper.tex: all
original calls, including zero cases, fit the single column reserve
when multiplied by their actual maximum physical budget. -/
theorem repeated_entry_budget_selected {B1 B2 : ℕ} (E : EntryProducer B1 B2)
    (h : EntryBudgetBound E.1) : SelectedBudget (fun r=>(entryCalls r).length*entryMaximum E r) := by
  obtain ⟨K,e,hK⟩:=h
  refine ⟨2*K,e,fun r=>?_⟩
  have hm:=entryMaximum_uniform E K e hK r
  have hs:=entry_squared_reserve_add (firstActualEntry r)
  simp only [entryCalls,List.length_ofFn]
  calc
    _≤r.child.cellCall.seed.N^8*(K*(r.child.call.n+1)^e*
      (r.child.selected.1.Uocc^(2*(firstActualEntry r).degree)+1)):=Nat.mul_le_mul_left _ hm
    _=K*(r.child.call.n+1)^e*(r.child.cellCall.seed.N^8*
      (r.child.selected.1.Uocc^(2*(firstActualEntry r).degree)+1)):=by ring
    _≤K*(r.child.call.n+1)^e*(2*2^(r.child.call.n-r.child.selected.1.k)):=
      Nat.mul_le_mul_left _ hs
    _=_:=by ring

theorem walk_count_selected (B1 B2 : ℕ) :
    SelectedBudget (B1:=B1) (B2:=B2) (fun r=>(entryCalls r).length) := by
  refine ⟨1,0,fun r=>?_⟩
  simpa only [entryCalls,List.length_ofFn,Nat.one_mul,Nat.mul_one,pow_zero] using
    StageLiftSourceCost.walkCount_le_columns r

end NearQuarticWires.StageGreedyCollector
