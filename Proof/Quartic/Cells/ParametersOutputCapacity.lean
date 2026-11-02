import Proof.Quartic.Cells.ParametersOutputCapacityLeaves

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Dispatch
open StageOutput

/-- Each of the literal numerator expressions of Step 5 has at
most fourteen units in its binary exponent census, `sec:algorithm`, paper/paper.tex. -/
theorem output_numerator_expression_capacity (e : AE) (B W : ℕ) (env : Fin VV → ℕ)
    (hw : 64 * (B + 1) ≤ W) (he : outputExpressionWeight e ≤ 14)
    (hleaf : outputExpressionLeaves (2 * B + 2) env e) :
    e.eval env ≤ 2 ^ (28 * (B + 1)) ∧ e.ok W env := by
  have hweight : outputExpressionWeight e * (2 * B + 2) ≤ 28 * (B + 1) := by
    have hh := Nat.mul_le_mul_right (2 * B + 2) he
    nlinarith only [hh]
  have hw' : outputExpressionWeight e * (2 * B + 2) < W := hweight.trans_lt (by omega)
  have hc := output_expression_capacity e (2 * B + 2) W env (by omega) hleaf hw'
  exact ⟨hc.1.trans (Nat.pow_le_pow_right (by norm_num) hweight), hc.2⟩

/-- The exact sequential lower-numerator program has no arithmetic
overflow under the charged width, Step 5 and `prop:time`,
paper/paper.tex. -/
theorem output_lower_assignments_safe (d : Input) (B W : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hk : d.k ≤ B) (hw : 64 * (B + 1) ≤ W)
    (hs : d.Stored env) (hpower : env powerK = 2 ^ d.k) :
    assignmentsSafe W lowerAssignments env := by
  have hl := output_basic_expression_leaves d B env hf hk hs hpower
  have hD := (output_numerator_expression_capacity denominatorExpr B W env hw (by decide) hl.1).2
  have hX := (output_numerator_expression_capacity lowerPositiveExpr B W env hw (by decide) hl.2.1).2
  have hY := (output_numerator_expression_capacity lowerNegativeExpr B W env hw (by decide) hl.2.2.1).2
  simpa (config := { decide := true }) [assignmentsSafe, lowerAssignments,
    denominatorExpr, lowerPositiveExpr, lowerNegativeExpr, AE.ok, AE.eval,
    roundD, roundX, powerK, Function.update] using
    (show denominatorExpr.ok W env ∧ lowerPositiveExpr.ok W env ∧ lowerNegativeExpr.ok W env ∧ True from
      ⟨hD, hX, hY, trivial⟩)

/-- The exact sequential upper-numerator program has no arithmetic
overflow after the denominator is stored, Step 5 and `prop:time`,
paper/paper.tex. -/
theorem output_upper_assignments_safe (d : Input) (B W : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hn : d.n ≤ B) (hk : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ W) (hs : d.Stored env)
    (hpowerN : env powerN = 2 ^ d.n) (hpowerK : env powerK = 2 ^ d.k)
    (hD : env roundD = d.denominator) : assignmentsSafe W upperAssignments env := by
  have hl := output_basic_expression_leaves d B env hf hk hs hpowerK
  have hu := output_upper_expression_leaves d B env hf hn hk hs hpowerN hpowerK hD
  have hX := (output_numerator_expression_capacity upperPositiveExpr B W env hw (by decide) hu).2
  have hY := (output_numerator_expression_capacity upperNegativeExpr B W env hw (by decide) hl.2.2.2).2
  simpa (config := { decide := true }) [assignmentsSafe, upperAssignments,
    upperPositiveExpr, upperNegativeExpr, AE.ok, AE.eval,
    roundD, roundX, powerK, powerN, Function.update] using
    (show upperPositiveExpr.ok W env ∧ upperNegativeExpr.ok W env ∧ True from ⟨hX, hY, trivial⟩)

end NearQuarticWires.Cells
