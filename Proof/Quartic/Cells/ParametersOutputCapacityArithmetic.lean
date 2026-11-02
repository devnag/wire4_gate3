import Proof.Quartic.StageOutput.Numerators

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Dispatch

/-- An exponent census for the addition and multiplication
expressions of Step 5, `sec:algorithm`, paper/paper.tex. -/
def outputExpressionWeight : AE → ℕ
  | .var _ => 1
  | .lit _ => 1
  | .add e f => outputExpressionWeight e + outputExpressionWeight f + 1
  | .sub e f => outputExpressionWeight e + outputExpressionWeight f
  | .mul e f => outputExpressionWeight e + outputExpressionWeight f
  | .div _ _ => 1
  | .mod _ _ => 1

/-- Literal and variable range bounds for the numerator expressions
of Step 5, `sec:algorithm`, paper/paper.tex. Division is handled by
the separate signed rounding program. -/
def outputExpressionLeaves (L : ℕ) (env : Fin VV → ℕ) : AE → Prop
  | .var x => env x ≤ 2 ^ L
  | .lit k => k ≤ 2 ^ L
  | .add e f => outputExpressionLeaves L env e ∧ outputExpressionLeaves L env f
  | .sub e f => outputExpressionLeaves L env e ∧ outputExpressionLeaves L env f
  | .mul e f => outputExpressionLeaves L env e ∧ outputExpressionLeaves L env f
  | .div _ _ => False
  | .mod _ _ => False

/-- The expression census is positive at every node, Step 5,
`sec:algorithm`, paper/paper.tex. -/
theorem outputExpressionWeight_pos (e : AE) : 0 < outputExpressionWeight e := by
  induction e <;> simp_all [outputExpressionWeight]

/-- A binary magnitude bound for an addition in Step 5,
`sec:algorithm`, paper/paper.tex. -/
theorem output_add_power_bound (x y a b : ℕ) (hx : x ≤ 2 ^ a) (hy : y ≤ 2 ^ b) :
    x + y ≤ 2 ^ (a + b + 1) := by
  have ha := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.le_add_right a b)
  have hb := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (Nat.le_add_left b a)
  calc
    x + y ≤ 2 ^ (a + b) + 2 ^ (a + b) := Nat.add_le_add (hx.trans ha) (hy.trans hb)
    _ = 2 ^ (a + b + 1) := by rw [pow_succ]; omega

/-- Every intermediate of the actual numerator expression fits
the assigned width when its exponent census fits, Step 5 and
`prop:time`, paper/paper.tex. -/
theorem output_expression_capacity (e : AE) (L W : ℕ) (env : Fin VV → ℕ)
    (hL : 1 ≤ L) (hleaf : outputExpressionLeaves L env e)
    (hW : outputExpressionWeight e * L < W) :
    e.eval env ≤ 2 ^ (outputExpressionWeight e * L) ∧ e.ok W env := by
  induction e with
  | var x => simpa only [AE.eval, AE.ok, outputExpressionWeight, outputExpressionLeaves, one_mul, and_true] using hleaf
  | lit k =>
    have hk : k ≤ 2 ^ L := hleaf
    have hw : L < W := by simpa only [outputExpressionWeight, one_mul] using hW
    exact ⟨by simpa only [AE.eval, outputExpressionWeight, one_mul] using hk,
      hk.trans_lt (Nat.pow_lt_pow_right (by norm_num) hw)⟩
  | add e f ihe ihf =>
    have heW : outputExpressionWeight e * L < W := by simp only [outputExpressionWeight] at hW; nlinarith only [hW, Nat.zero_le (outputExpressionWeight f * L), hL]
    have hfW : outputExpressionWeight f * L < W := by simp only [outputExpressionWeight] at hW; nlinarith only [hW, Nat.zero_le (outputExpressionWeight e * L), hL]
    have he := ihe hleaf.1 heW
    have hf := ihf hleaf.2 hfW
    have hv : e.eval env + f.eval env ≤ 2 ^ ((outputExpressionWeight e + outputExpressionWeight f + 1) * L) :=
      (output_add_power_bound _ _ _ _ he.1 hf.1).trans
        (Nat.pow_le_pow_right (by norm_num) (by nlinarith only [hL]))
    exact ⟨hv, he.2, hf.2, hv.trans_lt (Nat.pow_lt_pow_right (by norm_num) hW)⟩
  | sub e f ihe ihf =>
    have heW : outputExpressionWeight e * L < W := by simp only [outputExpressionWeight] at hW; nlinarith only [hW, Nat.zero_le (outputExpressionWeight f * L)]
    have hfW : outputExpressionWeight f * L < W := by simp only [outputExpressionWeight] at hW; nlinarith only [hW, Nat.zero_le (outputExpressionWeight e * L)]
    have he := ihe hleaf.1 heW
    have hf := ihf hleaf.2 hfW
    refine ⟨(Nat.sub_le _ _).trans (he.1.trans ?_), he.2, hf.2⟩
    exact Nat.pow_le_pow_right (by norm_num) (by simp only [outputExpressionWeight]; nlinarith only [Nat.zero_le (outputExpressionWeight f * L)])
  | mul e f ihe ihf =>
    have heW : outputExpressionWeight e * L < W := by simp only [outputExpressionWeight] at hW; nlinarith only [hW, Nat.zero_le (outputExpressionWeight f * L)]
    have hfW : outputExpressionWeight f * L < W := by simp only [outputExpressionWeight] at hW; nlinarith only [hW, Nat.zero_le (outputExpressionWeight e * L)]
    have he := ihe hleaf.1 heW
    have hf := ihf hleaf.2 hfW
    have hv : e.eval env * f.eval env ≤ 2 ^ ((outputExpressionWeight e + outputExpressionWeight f) * L) := by
      calc
        e.eval env * f.eval env ≤ 2 ^ (outputExpressionWeight e * L) * 2 ^ (outputExpressionWeight f * L) := Nat.mul_le_mul he.1 hf.1
        _ = _ := by rw [← pow_add, Nat.add_mul]
    exact ⟨hv, he.2, hf.2, hv.trans_lt (Nat.pow_lt_pow_right (by norm_num) hW)⟩
  | div e f _ _ => exact hleaf.elim
  | mod e f _ _ => exact hleaf.elim

end NearQuarticWires.Cells
