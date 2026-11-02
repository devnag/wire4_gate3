import Proof.Quartic.Cells.ParametersRecoveryReserve

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `lem:print` and `prop:time`, paper/paper.tex: the six fixed powers introduced by source sizes
and compilation are polynomial in the original arity. -/
theorem formula_fixed_size_factor (n V : ℕ) (hV : V ≤ 34 * n ^ 4) :
    (V + 1) ^ 6 ≤ 35 ^ 6 * (n + 1) ^ 24 := by
  have hn4 : n ^ 4 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ n) _
  have h1 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hb : V + 1 ≤ 35 * (n + 1) ^ 4 := by nlinarith only [hV, hn4, h1]
  calc
    (V + 1) ^ 6 ≤ (35 * (n + 1) ^ 4) ^ 6 := Nat.pow_le_pow_left hb _
    _ = _ := by ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the mask-source contribution fits a cubic-degree
coefficient reserve, with its fixed excess kept polynomial in arity. -/
theorem formula_compiler_exponent_absorption (n V D X : ℕ)
    (hV : V ≤ 34 * n ^ 4) (hX : 16 * X ≤ D) :
    (V + 1) ^ (2 * D + 6 * X + 6) ≤
      (35 ^ 6 * (n + 1) ^ 24) * (V + 1) ^ (3 * D) := by
  have he : 2 * D + 6 * X ≤ 3 * D := by omega
  calc
    (V + 1) ^ (2 * D + 6 * X + 6) =
        (V + 1) ^ 6 * (V + 1) ^ (2 * D + 6 * X) := by rw [pow_add, Nat.mul_comm]
    _ ≤ (35 ^ 6 * (n + 1) ^ 24) * (V + 1) ^ (3 * D) :=
      Nat.mul_le_mul (formula_fixed_size_factor n V hV)
        (Nat.pow_le_pow_right (Nat.succ_pos V) he)

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.ParameterRules

/-- `lem:print` and `prop:time`, paper/paper.tex: the all-walk expanded size exponent fits the unchanged
column reserve after retaining only a fixed arity polynomial. -/
theorem formula_all_walks_reserve {x : ParameterInput} {p : Parameters}
    (hs : ParameterRules x p) (V D X : ℕ)
    (hV : V ≤ 34 * x.n ^ 4) (hOcc : V + 1 ≤ p.Uocc)
    (hD : D ≤ p.Dmax) (hX : 16 * X ≤ D) :
    2 ^ (4 * p.k) * (V + 1) ^ (2 * D + 6 * X + 6) ≤
      (35 ^ 6 * (x.n + 1) ^ 24) * 2 ^ (x.n - p.k) := by
  calc
    _ ≤ 2 ^ (4 * p.k) * ((35 ^ 6 * (x.n + 1) ^ 24) * (V + 1) ^ (3 * D)) :=
      Nat.mul_le_mul_left _
        (ParameterArithmetic.formula_compiler_exponent_absorption x.n V D X hV hX)
    _ = (35 ^ 6 * (x.n + 1) ^ 24) * (2 ^ (4 * p.k) * (V + 1) ^ (3 * D)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (hs.recovery_all_walks_reserve V D hOcc hD)

end NearQuarticWires.Cells.ParameterRules
