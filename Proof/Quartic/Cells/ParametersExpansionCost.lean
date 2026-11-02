import Proof.Quartic.Cells.ParametersRecoveryReserve
import Proof.Gates.Expand.Machine

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `lem:print` and `prop:time`, paper/paper.tex: the fixed eighth and third powers in the concrete
expansion engine contribute only an arity polynomial of degree44. -/
theorem expansion_fixed_factors (n V : ℕ) (hV : V ≤ 34 * n ^ 4) :
    (V + 1) ^ 8 * (V + 2) ^ 3 ≤ 35 ^ 8 * 36 ^ 3 * (n + 1) ^ 44 := by
  have hn4 : n ^ 4 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_left (Nat.le_succ n) _
  have h1 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hb1 : V + 1 ≤ 35 * (n + 1) ^ 4 := by nlinarith only [hV, hn4, h1]
  have hb2 : V + 2 ≤ 36 * (n + 1) ^ 4 := by nlinarith only [hV, hn4, h1]
  calc
    (V + 1) ^ 8 * (V + 2) ^ 3 ≤
        (35 * (n + 1) ^ 4) ^ 8 * (36 * (n + 1) ^ 4) ^ 3 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hb1 _) (Nat.pow_le_pow_left hb2 _)
    _ = _ := by ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal eighth-power source factor combines
with the engine's degree factor inside a cubic-degree reserve. -/
theorem expansion_cost_factor_bound (n V D X A d S : ℕ)
    (hV : V ≤ 34 * n ^ 4) (hX : 16 * X ≤ D)
    (hS : S ≤ A * (n + 1) ^ d * (V + 1) ^ (X + 1)) :
    (V + 2) ^ (2 * D + 3) * S ^ 8 ≤
      (A ^ 8 * 35 ^ 8 * 36 ^ 3) * (n + 1) ^ (8 * d + 44) *
        (V + 2) ^ (3 * D) := by
  have hsource : S ^ 8 ≤ A ^ 8 * (n + 1) ^ (8 * d) *
      ((V + 1) ^ (8 * X) * (V + 1) ^ 8) := by
    calc
      S ^ 8 ≤ (A * (n + 1) ^ d * (V + 1) ^ (X + 1)) ^ 8 :=
        Nat.pow_le_pow_left hS _
      _ = A ^ 8 * (n + 1) ^ (d * 8) * (V + 1) ^ ((X + 1) * 8) := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      _ = _ := by
        rw [show d * 8 = 8 * d by omega, show (X + 1) * 8 = 8 * X + 8 by omega, pow_add]
  have hpower : (V + 2) ^ (2 * D) * (V + 1) ^ (8 * X) ≤ (V + 2) ^ (3 * D) := by
    calc
      _ ≤ (V + 2) ^ (2 * D) * (V + 2) ^ (8 * X) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (V + 2) ^ (2 * D + 8 * X) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    (V + 2) ^ (2 * D + 3) * S ^ 8 ≤ (V + 2) ^ (2 * D + 3) *
        (A ^ 8 * (n + 1) ^ (8 * d) * ((V + 1) ^ (8 * X) * (V + 1) ^ 8)) :=
      Nat.mul_le_mul_left _ hsource
    _ = (A ^ 8 * (n + 1) ^ (8 * d)) *
        ((V + 2) ^ (2 * D) * (V + 1) ^ (8 * X)) *
        ((V + 1) ^ 8 * (V + 2) ^ 3) := by rw [pow_add]; ring
    _ ≤ (A ^ 8 * (n + 1) ^ (8 * d)) * (V + 2) ^ (3 * D) *
        (35 ^ 8 * 36 ^ 3 * (n + 1) ^ 44) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hpower) (expansion_fixed_factors n V hV)
    _ = _ := by rw [pow_add]; ring

end NearQuarticWires.Cells.ParameterArithmetic

namespace NearQuarticWires.Cells.ParameterRules

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual concrete expansion-machine budget,
summed over all closed walks, fits a fixed arity polynomial times
the column reserve when its literal source and AST bounds hold. -/
theorem expansionMachine_all_walks_budget {x : ParameterInput} {p : Parameters}
    (hs : ParameterRules x p) (V D X A d : ℕ) (F : Formula V)
    (hdegree : F.degree ≤ D) (hD : D ≤ p.Dmax) (hX : 16 * X ≤ D)
    (hV : V ≤ 34 * x.n ^ 4) (hOcc : V + 2 ≤ p.Uocc)
    (hsource : (formulaWord ⟨V, F⟩).length + F.size + F.weight + 1 ≤
      A * (x.n + 1) ^ d * (V + 1) ^ (X + 1)) :
    2 ^ (4 * p.k) * NearCubicGates.Close.Expand.expansionMachine.budget ⟨V, F⟩ ≤
      (10 ^ 11 * A ^ 8 * 35 ^ 8 * 36 ^ 3) * (x.n + 1) ^ (8 * d + 44) *
        2 ^ (x.n - p.k) := by
  have hbudget := NearCubicGates.Close.Expand.Layout.budget_le (⟨V, F⟩ : FormulaReq)
  have hdegreePow : (V + 2) ^ (2 * F.degree + 3) ≤ (V + 2) ^ (2 * D + 3) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hshape := ParameterArithmetic.expansion_cost_factor_bound x.n V D X A d
    ((formulaWord ⟨V, F⟩).length + F.size + F.weight + 1) hV hX hsource
  have hconcrete : NearCubicGates.Close.Expand.expansionMachine.budget ⟨V, F⟩ ≤
      (10 ^ 11 * A ^ 8 * 35 ^ 8 * 36 ^ 3) * (x.n + 1) ^ (8 * d + 44) *
        (V + 2) ^ (3 * D) := by
    calc
      _ ≤ 10 ^ 11 * (V + 2) ^ (2 * F.degree + 3) *
          ((formulaWord ⟨V, F⟩).length + F.size + F.weight + 1) ^ 8 := hbudget
      _ ≤ 10 ^ 11 * ((V + 2) ^ (2 * D + 3) *
          ((formulaWord ⟨V, F⟩).length + F.size + F.weight + 1) ^ 8) := by
        exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdegreePow)).trans_eq (by ring)
      _ ≤ 10 ^ 11 * ((A ^ 8 * 35 ^ 8 * 36 ^ 3) * (x.n + 1) ^ (8 * d + 44) *
          (V + 2) ^ (3 * D)) := Nat.mul_le_mul_left _ hshape
      _ = _ := by ring
  have hreserve : 2 ^ (4 * p.k) * (V + 2) ^ (3 * D) ≤ 2 ^ (x.n - p.k) :=
    hs.recovery_all_walks_reserve (V + 1) D hOcc hD
  calc
    _ ≤ 2 ^ (4 * p.k) * ((10 ^ 11 * A ^ 8 * 35 ^ 8 * 36 ^ 3) *
        (x.n + 1) ^ (8 * d + 44) * (V + 2) ^ (3 * D)) := Nat.mul_le_mul_left _ hconcrete
    _ = ((10 ^ 11 * A ^ 8 * 35 ^ 8 * 36 ^ 3) * (x.n + 1) ^ (8 * d + 44)) *
        (2 ^ (4 * p.k) * (V + 2) ^ (3 * D)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hreserve

end NearQuarticWires.Cells.ParameterRules
