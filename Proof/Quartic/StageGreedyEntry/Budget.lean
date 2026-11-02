import Proof.Quartic.StageGreedyCollector.PerEntryTarget
import Proof.Quartic.Control.GammaControl

/-!
# Closure of the selected per-entry clock

Paper: `prop:time`, paper/paper.tex.

The selected per-entry bound `K (n+1)^e (Uocc^(2D)+1)` is closed under sums, fixed multiples, larger
fixed exponents and the composition clock `4 bf + 4 bg + 12` of two ordinary programs.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open StagePrint StageGreedyCollector

variable {B1 B2 : ℕ}

theorem ebb_mono {b b' : GreedyEntry.Request B1 B2→ℕ} (h : EntryBudgetBound b)
    (hle : ∀r,b' r≤b r) : EntryBudgetBound b' := by
  obtain ⟨K,e,hK⟩:=h
  exact ⟨K,e,fun r=>(hle r).trans (hK r)⟩

/-- A larger exponent dominates a smaller one. -/
theorem lift_exp (n K e e' U : ℕ) (h : e≤e') : K*(n+1)^e*U≤K*(n+1)^e'*U :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) h))

theorem ebb_add {b b' : GreedyEntry.Request B1 B2→ℕ} (h : EntryBudgetBound b)
    (h' : EntryBudgetBound b') : EntryBudgetBound (fun r=>b r+b' r) := by
  obtain ⟨K,e,hK⟩:=h
  obtain ⟨K',e',hK'⟩:=h'
  refine ⟨K+K',e+e',fun r=>?_⟩
  have h1:=(hK r).trans (lift_exp r.source.child.call.n K e (e+e')
    (r.source.child.selected.1.Uocc^(2*r.degree)+1) (by omega))
  have h2:=(hK' r).trans (lift_exp r.source.child.call.n K' e' (e+e')
    (r.source.child.selected.1.Uocc^(2*r.degree)+1) (by omega))
  calc
    _≤K*(r.source.child.call.n+1)^(e+e')*(r.source.child.selected.1.Uocc^(2*r.degree)+1)+
        K'*(r.source.child.call.n+1)^(e+e')*(r.source.child.selected.1.Uocc^(2*r.degree)+1) :=
      Nat.add_le_add h1 h2
    _=_ := by ring

theorem ebb_const (c : ℕ) : EntryBudgetBound (fun _ : GreedyEntry.Request B1 B2=>c) :=
  ⟨c,0,fun r=>by
    simp only [pow_zero,Nat.mul_one]
    exact Nat.le_mul_of_pos_right _ (by omega)⟩

theorem ebb_smul {b : GreedyEntry.Request B1 B2→ℕ} (h : EntryBudgetBound b) (c : ℕ) :
    EntryBudgetBound (fun r=>c*b r) := by
  obtain ⟨K,e,hK⟩:=h
  refine ⟨c*K,e,fun r=>?_⟩
  calc
    _≤c*(K*(r.source.child.call.n+1)^e*(r.source.child.selected.1.Uocc^(2*r.degree)+1)) :=
      Nat.mul_le_mul_left _ (hK r)
    _=_ := by ring

/-- `prop:time`, paper/paper.tex: the composition clock. -/
theorem ebb_pipe {bf bg : GreedyEntry.Request B1 B2→ℕ} (hf : EntryBudgetBound bf)
    (hg : EntryBudgetBound bg) : EntryBudgetBound (fun r=>4*bf r+4*bg r+12) :=
  ebb_add (ebb_add (ebb_smul hf 4) (ebb_smul hg 4)) (ebb_const 12)

/-- A polynomial in the original arity alone. -/
theorem ebb_arity (K e : ℕ) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>K*(r.source.child.call.n+1)^e) :=
  ⟨K,e,fun r=>Nat.le_mul_of_pos_right _ (by omega)⟩

end NearQuarticWires.StageGreedyEntry
