import Proof.Quartic.StageOutput.Assignments
import Proof.Quartic.StageOutput.Layout
import Proof.Gates.Dispatch.ParamsA

/-!
# Scalar preservation through the arithmetic of Step 5

Paper: `sec:algorithm`, paper/paper.tex. The fixed
arithmetic expressions write only their stated destinations. In particular,
the thirteen parsed input fields remain available to both endpoint formulas.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicGates.Close.Dispatch

theorem assignmentEnv_preserved (xs : List Assignment) (env : Fin VV → ℕ)
    (y : Fin VV) (hy : y ∉ xs.map Prod.fst) : assignmentEnv xs env y = env y := by
  induction xs generalizing env with
  | nil => rfl
  | cons p xs ih =>
    have hh : y ≠ p.1 ∧ y ∉ xs.map Prod.fst := by simpa using hy
    exact (ih _ hh.2).trans (Function.update_of_ne hh.1 _ _)

theorem assignmentProgram_frame {xs : List Assignment} {a b : DS VV}
    (h : lowAgree (assignmentEnv xs a.env) b.env) :
    FrS a b (vJ :: xs.map Prod.fst) := by
  intro y hy hn
  have hh : y ≠ vJ ∧ y ∉ xs.map Prod.fst := by simpa using hn
  exact (h y hy hh.1).trans (assignmentEnv_preserved xs a.env y hh.2)

theorem Input.stored_congr (d : Input) {a b : Fin VV → ℕ} (ha : d.Stored a)
    (h : ∀ x ∈ inputVariables, b x = a x) : d.Stored b := by
  simp only [Input.Stored] at ha ⊢
  simpa only [h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide),
    h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide),
    h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide),
    h 32 (by decide)] using ha

theorem Input.stored_of_frame (d : Input) {a b : DS VV} {scratch : List (Fin VV)}
    (ha : d.Stored a.env) (h : FrS a b scratch)
    (hdis : ∀ x ∈ inputVariables, x ∉ scratch) : d.Stored b.env := by
  apply d.stored_congr ha
  intro x hx
  have hlow : x.val < 200 := by
    simp only [inputVariables, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h x hlow (hdis x hx)

end NearQuarticWires.StageOutput
