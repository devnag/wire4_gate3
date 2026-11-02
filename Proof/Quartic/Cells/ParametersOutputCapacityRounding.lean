import Proof.Quartic.Cells.ParametersOutputCapacity

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Dispatch
open StageOutput

/-- The literal expression values are the stored integer operands
of Step 5, `sec:algorithm`, paper/paper.tex. -/
theorem output_basic_expression_values (d : Input) (env : Fin VV → ℕ)
    (hs : d.Stored env) (hk : env powerK = 2 ^ d.k) :
    denominatorExpr.eval env = d.denominator ∧
      lowerPositiveExpr.eval env = d.lowerPositive ∧
      lowerNegativeExpr.eval env = d.lowerNegative ∧
      upperNegativeExpr.eval env = d.upperNegative := by
  obtain ⟨_, _, hQ, hMF, _, hNum, hDen, hnc, _, _, hA, _, hM⟩ := hs
  simp only [denominatorExpr, lowerPositiveExpr, lowerNegativeExpr, upperNegativeExpr,
    AE.eval, hQ, hMF, hNum, hDen, hnc, hA, hM, hk,
    Input.denominator, Input.lowerPositive, Input.lowerNegative, Input.upperNegative,
    and_self]

/-- The upper positive expression is the exact stored numerator,
Step 5, `sec:algorithm`, paper/paper.tex. -/
theorem output_upper_expression_value (d : Input) (env : Fin VV → ℕ)
    (hs : d.Stored env) (hn : env powerN = 2 ^ d.n) (hk : env powerK = 2 ^ d.k)
    (hD : env roundD = d.denominator) : upperPositiveExpr.eval env = d.upperPositive := by
  obtain ⟨_, _, hQ, hMF, _, hNum, hDen, hnc, _, _, hA, _, _⟩ := hs
  simp only [upperPositiveExpr, AE.eval, hQ, hMF, hNum, hDen, hnc, hA, hn, hk, hD,
    Input.upperPositive]

/-- Three numerator magnitudes of the allotted size satisfy the
rounding program's exact addition and division guards, Step 5,
`prop:sound`, paper/paper.tex. -/
theorem output_rounding_capacity_of_bounds (X Y D B W : ℕ)
    (hw : 64 * (B + 1) ≤ W) (hX : X ≤ 2 ^ (28 * (B + 1)))
    (hY : Y ≤ 2 ^ (28 * (B + 1))) (hD : D ≤ 2 ^ (28 * (B + 1))) :
    X + Y + D + 2 < 2 ^ W ∧ 2 * D ≤ 2 ^ W := by
  have htwo : 2 ≤ (2 : ℕ) ^ (28 * (B + 1)) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (by omega : 1 ≤ 28 * (B + 1))
  constructor
  · calc
      X + Y + D + 2 ≤ 4 * 2 ^ (28 * (B + 1)) := by omega
      _ = 2 ^ (28 * (B + 1) + 2) := by rw [pow_add]; norm_num; ring
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · calc
      2 * D ≤ 2 * 2 ^ (28 * (B + 1)) := Nat.mul_le_mul_left _ hD
      _ = 2 ^ (28 * (B + 1) + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The actual lower endpoint operands satisfy all arithmetic
capacity conditions of the signed rounding program, Step 5,
`prop:sound`, paper/paper.tex. -/
theorem output_lower_rounding_capacity (d : Input) (B W : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hk : d.k ≤ B) (hw : 64 * (B + 1) ≤ W)
    (hs : d.Stored env) (hpower : env powerK = 2 ^ d.k) :
    d.lowerPositive + d.lowerNegative + d.denominator + 2 < 2 ^ W ∧
      2 * d.denominator ≤ 2 ^ W := by
  have hl := output_basic_expression_leaves d B env hf hk hs hpower
  have hv := output_basic_expression_values d env hs hpower
  have hD := (output_numerator_expression_capacity denominatorExpr B W env hw (by decide) hl.1).1
  have hX := (output_numerator_expression_capacity lowerPositiveExpr B W env hw (by decide) hl.2.1).1
  have hY := (output_numerator_expression_capacity lowerNegativeExpr B W env hw (by decide) hl.2.2.1).1
  rw [hv.1] at hD
  rw [hv.2.1] at hX
  rw [hv.2.2.1] at hY
  exact output_rounding_capacity_of_bounds _ _ _ B W hw hX hY hD

/-- The actual upper endpoint operands satisfy all arithmetic
capacity conditions of the signed rounding program, Step 5,
`prop:sound`, paper/paper.tex. -/
theorem output_upper_rounding_capacity (d : Input) (B W : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hn : d.n ≤ B) (hk : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ W) (hs : d.Stored env)
    (hpowerN : env powerN = 2 ^ d.n) (hpowerK : env powerK = 2 ^ d.k)
    (hD : env roundD = d.denominator) :
    d.upperPositive + d.upperNegative + d.denominator + 2 < 2 ^ W ∧
      2 * d.denominator ≤ 2 ^ W := by
  have hl := output_basic_expression_leaves d B env hf hk hs hpowerK
  have hu := output_upper_expression_leaves d B env hf hn hk hs hpowerN hpowerK hD
  have hv := output_basic_expression_values d env hs hpowerK
  have hden := (output_numerator_expression_capacity denominatorExpr B W env hw (by decide) hl.1).1
  have hX := (output_numerator_expression_capacity upperPositiveExpr B W env hw (by decide) hu).1
  have hY := (output_numerator_expression_capacity upperNegativeExpr B W env hw (by decide) hl.2.2.2).1
  rw [hv.1] at hden
  rw [output_upper_expression_value d env hs hpowerN hpowerK hD] at hX
  rw [hv.2.2.2] at hY
  exact output_rounding_capacity_of_bounds _ _ _ B W hw hX hY hden

/-- The dyadic denominator and both spare rounding bits fit the
charged width, Step 5 and `prop:time`, paper/paper.tex. -/
theorem output_dyadic_capacity (n B W : ℕ) (hn : n ≤ B) (hw : 64 * (B + 1) ≤ W) :
    2 ^ (n + 2) < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)

end NearQuarticWires.Cells
