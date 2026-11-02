import Proof.Quartic.StagePrep.ParameterRegisters

/-!
# Exact parameter register contents

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- Exact contents of a finite public register collection in
`sec:params`, paper/paper.tex. -/
def RegisterValues (a : DS VV) (xs : List (Fin VV × ℕ)) : Prop :=
  ∀ x ∈ xs, a.env x.1 = x.2

/-- Concatenating register collections in `sec:params`,
paper/paper.tex, retains every stated value. -/
theorem registerValues_append (a : DS VV) (xs ys : List (Fin VV × ℕ)) :
    RegisterValues a (xs ++ ys) ↔ RegisterValues a xs ∧ RegisterValues a ys := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left _ hx),
      fun x hx => h x (List.mem_append_right _ hx)⟩
  · rintro ⟨hx, hy⟩ x hxy
    rcases List.mem_append.1 hxy with h | h
    · exact hx x h
    · exact hy x h

/-- The untouched registers of `sec:params`, paper/paper.tex, retain their exact public values across an
executed arithmetic subroutine. -/
theorem registerValues_preserved {a b : DS VV} {xs : List (Fin VV × ℕ)}
    {T : List (Fin VV)} (h : RegisterValues a xs) (hf : FrS a b T)
    (hsafe : ∀ x ∈ xs, x.1.val < 200 ∧ x.1 ∉ T) : RegisterValues b xs := by
  intro x hx
  exact (hf x.1 (hsafe x hx).1 (hsafe x hx).2).trans (h x hx)

/-- A single entry in the exact public register collection
of `sec:params`, paper/paper.tex. -/
theorem registerValues_cons (a : DS VV) (r : Fin VV) (v : ℕ)
    (xs : List (Fin VV × ℕ)) :
    RegisterValues a ((r, v) :: xs) ↔ a.env r = v ∧ RegisterValues a xs := by
  simp only [RegisterValues, List.mem_cons, forall_eq_or_imp]

end NearQuarticWires.StagePrep
