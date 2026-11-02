import Proof.Quartic.Cells.ParametersOutputCapacityArithmetic

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Dispatch
open StageOutput

/-- Every stored field has the literal value in the Step 5 codec,
`sec:algorithm`, paper/paper.tex. -/
theorem output_stored_field_eq (d : Input) (env : Fin VV → ℕ) (hs : d.Stored env) :
    ∀ xv ∈ d.fields, env xv.1 = xv.2 := by
  obtain ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩ := hs
  intro xv hx
  simp only [Input.fields, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    assumption

/-- The parsed Step 5 scalar ranges lift to the arithmetic width
used by its numerator expressions, `sec:algorithm`, paper/paper.tex. -/
theorem output_stored_field_bound (d : Input) (B : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hs : d.Stored env) :
    ∀ xv ∈ d.fields, env xv.1 ≤ 2 ^ (2 * B + 2) := by
  intro xv hx
  rw [output_stored_field_eq d env hs xv hx]
  exact (hf xv hx).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The denominator itself has the common scalar binary width,
Step 5, `sec:algorithm`, paper/paper.tex. -/
theorem output_denominator_bound (d : Input) (B : ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) : d.denominator ≤ 2 ^ (2 * B + 2) := by
  have hQ := (hf (22, d.Q) (by simp [Input.fields])).le
  have hD := (hf (26, d.etaDen) (by simp [Input.fields])).le
  calc
    d.denominator ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul hQ hD
    _ = 2 ^ (2 * B) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- All leaves of the lower numerator assignments are bounded
before any assignment executes, Step 5, `sec:algorithm`, paper/paper.tex. No bound on unused registers is required. -/
theorem output_basic_expression_leaves (d : Input) (B : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hk : d.k ≤ B)
    (hs : d.Stored env) (hpower : env powerK = 2 ^ d.k) :
    outputExpressionLeaves (2 * B + 2) env denominatorExpr ∧
      outputExpressionLeaves (2 * B + 2) env lowerPositiveExpr ∧
      outputExpressionLeaves (2 * B + 2) env lowerNegativeExpr ∧
      outputExpressionLeaves (2 * B + 2) env upperNegativeExpr := by
  have fields := output_stored_field_bound d B env hf hs
  have hQ := fields (22, d.Q) (by simp [Input.fields])
  have hMF := fields (23, d.MF) (by simp [Input.fields])
  have hnum := fields (25, d.etaNum) (by simp [Input.fields])
  have hden := fields (26, d.etaDen) (by simp [Input.fields])
  have hnc := fields (27, d.nc) (by simp [Input.fields])
  have hA := fields (30, d.A) (by simp [Input.fields])
  have hM := fields (32, d.M) (by simp [Input.fields])
  have hp : env powerK ≤ 2 ^ (2 * B + 2) := by
    rw [hpower]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ≤ (2 : ℕ) ^ (2 * B + 2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ 2 * B + 2)
  exact ⟨⟨hQ, hden⟩, ⟨⟨hp, hA⟩, hden⟩,
    ⟨⟨⟨⟨⟨hp, htwo⟩, hMF⟩, hnc⟩, hnum⟩, hQ⟩, ⟨⟨hp, hM⟩, hden⟩⟩

/-- All leaves of the upper positive numerator include the already
computed denominator and both dyadic powers, Step 5,
`sec:algorithm`, paper/paper.tex. -/
theorem output_upper_expression_leaves (d : Input) (B : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hn : d.n ≤ B) (hk : d.k ≤ B)
    (hs : d.Stored env) (hpowerN : env powerN = 2 ^ d.n)
    (hpowerK : env powerK = 2 ^ d.k) (hD : env roundD = d.denominator) :
    outputExpressionLeaves (2 * B + 2) env upperPositiveExpr := by
  have fields := output_stored_field_bound d B env hf hs
  have hQ := fields (22, d.Q) (by simp [Input.fields])
  have hMF := fields (23, d.MF) (by simp [Input.fields])
  have hnum := fields (25, d.etaNum) (by simp [Input.fields])
  have hden := fields (26, d.etaDen) (by simp [Input.fields])
  have hnc := fields (27, d.nc) (by simp [Input.fields])
  have hA := fields (30, d.A) (by simp [Input.fields])
  have hpk : env powerK ≤ 2 ^ (2 * B + 2) := by
    rw [hpowerK]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpn : env powerN ≤ 2 ^ (2 * B + 2) := by
    rw [hpowerN]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : env roundD ≤ 2 ^ (2 * B + 2) := by rw [hD]; exact output_denominator_bound d B hf
  have htwo : 2 ≤ (2 : ℕ) ^ (2 * B + 2) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (by omega : 1 ≤ 2 * B + 2)
  have hone : 1 ≤ (2 : ℕ) ^ (2 * B + 2) := Nat.one_le_two_pow
  exact ⟨⟨hpk, ⟨⟨hA, hden⟩, ⟨⟨⟨⟨⟨htwo, hMF⟩, hone⟩, hnc⟩, hnum⟩, hQ⟩⟩⟩, ⟨hpn, hd⟩⟩

end NearQuarticWires.Cells
