import Proof.Gates.Dispatch.Expr

/-!
# Width bounds for the positive parameter products

Paper: the integer-power comparisons of `sec:params`,
paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- Positive product expressions in the exact integer parameter
rules of `sec:params`, paper/paper.tex. -/
def PositiveProduct (env : Fin VV → ℕ) : AE → Prop
  | .var x => 0 < env x
  | .lit k => 0 < k
  | .mul e f => PositiveProduct env e ∧ PositiveProduct env f
  | _ => False

/-- Every positive parameter product of `sec:params`,
paper/paper.tex, has positive exact value. -/
theorem positiveProduct_eval_pos (env : Fin VV → ℕ) (e : AE)
    (h : PositiveProduct env e) : 0 < e.eval env := by
  induction e with
  | var x => exact h
  | lit k => exact h
  | mul e f ihe ihf => exact Nat.mul_pos (ihe h.1) (ihf h.2)
  | add _ _ _ _ | sub _ _ _ _ | div _ _ _ _ | mod _ _ _ _ => exact False.elim h

/-- Every intermediate factor in the integer products of
`sec:params`, paper/paper.tex, fits a register
whenever their full positive product fits. -/
theorem positiveProduct_ok (env : Fin VV → ℕ) (e : AE) (Wd : ℕ)
    (h : PositiveProduct env e) (hcap : e.eval env < 2 ^ Wd) : e.ok Wd env := by
  induction e with
  | var x => trivial
  | lit k => exact hcap
  | mul e f ihe ihf =>
    have he := positiveProduct_eval_pos env e h.1
    have hf := positiveProduct_eval_pos env f h.2
    exact ⟨ihe h.1 ((Nat.le_mul_of_pos_right _ hf).trans_lt hcap),
      ihf h.2 ((Nat.le_mul_of_pos_left _ he).trans_lt hcap), hcap⟩
  | add _ _ _ _ | sub _ _ _ _ | div _ _ _ _ | mod _ _ _ _ => exact False.elim h

/-- A fixed natural power in the integer comparisons of
`sec:params`, paper/paper.tex. -/
def powerExpression (e : AE) : ℕ → AE
  | 0 => .lit 1
  | k + 1 => .mul (powerExpression e k) e

/-- The power expression for `sec:params`, paper/paper.tex, evaluates to the actual integer power. -/
theorem powerExpression_eval (env : Fin VV → ℕ) (e : AE) (k : ℕ) :
    (powerExpression e k).eval env = e.eval env ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [powerExpression, AE.eval, ih, pow_succ]

/-- The positive power expressions in `sec:params`,
paper/paper.tex, preserve positivity. -/
theorem powerExpression_positive (env : Fin VV → ℕ) (e : AE) (k : ℕ)
    (h : PositiveProduct env e) : PositiveProduct env (powerExpression e k) := by
  induction k with
  | zero => exact Nat.zero_lt_one
  | succ k ih => exact ⟨ih, h⟩

end NearQuarticWires.StagePrep
