import Proof.Quartic.StageGreedyCollector.SelectedReserve

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

/-- `prop:time`, paper/paper.tex: one
selected collector budget consists of the original outer-column count
times a fixed polynomial in original arity. -/
def SelectedBudget {B1 B2 : ℕ} (budget : Greedy.PrintRequest B1 B2→ℕ) : Prop :=
  ∃K e : ℕ,∀r,budget r≤K*2^(r.child.call.n-r.child.selected.1.k)*(r.child.call.n+1)^e

variable {B1 B2 : ℕ}

theorem SelectedBudget.const (c : ℕ) : SelectedBudget (B1:=B1) (B2:=B2) (fun _=>c) := by
  refine ⟨c,0,fun r=>?_⟩
  have h : 1≤2^(r.child.call.n-r.child.selected.1.k):=Nat.one_le_two_pow
  simpa only [pow_zero,Nat.mul_one] using Nat.le_mul_of_pos_right c h

theorem SelectedBudget.add {f g : Greedy.PrintRequest B1 B2→ℕ}
    (hf : SelectedBudget f) (hg : SelectedBudget g) : SelectedBudget (fun r=>f r+g r) := by
  obtain ⟨Kf,ef,hf⟩:=hf
  obtain ⟨Kg,eg,hg⟩:=hg
  refine ⟨Kf+Kg,ef+eg,fun r=>?_⟩
  have h1:=Nat.mul_le_mul_left (Kf*2^(r.child.call.n-r.child.selected.1.k))
    (Nat.pow_le_pow_right (by omega : 1≤r.child.call.n+1) (Nat.le_add_right ef eg))
  have h2:=Nat.mul_le_mul_left (Kg*2^(r.child.call.n-r.child.selected.1.k))
    (Nat.pow_le_pow_right (by omega : 1≤r.child.call.n+1) (Nat.le_add_left eg ef))
  have ha:=hf r
  have hb:=hg r
  nlinarith

theorem SelectedBudget.scale {f : Greedy.PrintRequest B1 B2→ℕ}
    (hf : SelectedBudget f) (c : ℕ) : SelectedBudget (fun r=>c*f r) := by
  obtain ⟨K,e,hK⟩:=hf
  refine ⟨c*K,e,fun r=>?_⟩
  have h:=Nat.mul_le_mul_left c (hK r)
  simpa only [Nat.mul_assoc] using h

theorem SelectedBudget.mono {f g : Greedy.PrintRequest B1 B2→ℕ}
    (hg : SelectedBudget g) (h : ∀r,f r≤g r) : SelectedBudget f := by
  obtain ⟨K,e,hK⟩:=hg
  exact ⟨K,e,fun r=>(h r).trans (hK r)⟩

end NearQuarticWires.StageGreedyCollector
