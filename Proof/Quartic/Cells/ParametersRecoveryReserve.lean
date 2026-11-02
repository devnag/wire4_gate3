import Proof.Quartic.Cells.ParametersBounds

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:print` and `sec:params`, paper/paper.tex: the unchanged degree guard pays fifty powers of
any actual variable scale below the occurrence census, together
with twice the closed-walk exponent. -/
theorem recovery_compiler_reserve (hs : ParameterRules x p) (V D : ℕ)
    (hV : V + 1 ≤ p.Uocc) (hD : D ≤ p.Dmax) :
    2 ^ (8 * p.k) * (V + 1) ^ (50 * D) ≤ 2 ^ (x.n - p.k) := by
  have hb := hs.degree_maximal.1
  unfold DegreePass at hb
  rw [hs.m_eq] at hb
  have hd := Nat.mul_le_mul_right (Nat.clog 2 p.Uocc) hD
  have he : 8 * p.k + 50 * D * Nat.clog 2 p.Uocc ≤ x.n - p.k := by
    nlinarith only [hb, hd, Nat.zero_le p.k, Nat.zero_le (D * Nat.clog 2 p.Uocc)]
  have hbase : V + 1 ≤ 2 ^ Nat.clog 2 p.Uocc :=
    hV.trans (Nat.le_pow_clog (by norm_num) _)
  calc
    2 ^ (8 * p.k) * (V + 1) ^ (50 * D) ≤
        2 ^ (8 * p.k) * (2 ^ Nat.clog 2 p.Uocc) ^ (50 * D) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
    _ = 2 ^ (8 * p.k + 50 * D * Nat.clog 2 p.Uocc) := by
      rw [← pow_mul, ← pow_add, Nat.mul_comm (Nat.clog 2 p.Uocc) (50 * D)]
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) he

/-- `lem:print` and `prop:time`, paper/paper.tex: a cubic-degree coefficient compiler may be summed
over all closed walks within the original column-entry reserve. -/
theorem recovery_all_walks_reserve (hs : ParameterRules x p) (V D : ℕ)
    (hV : V + 1 ≤ p.Uocc) (hD : D ≤ p.Dmax) :
    2 ^ (4 * p.k) * (V + 1) ^ (3 * D) ≤ 2 ^ (x.n - p.k) := by
  calc
    2 ^ (4 * p.k) * (V + 1) ^ (3 * D) ≤
        2 ^ (8 * p.k) * (V + 1) ^ (50 * D) := Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num) (by omega))
      (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ _ := hs.recovery_compiler_reserve V D hV hD

/-- `lem:print` and `prop:time`, paper/paper.tex: the square of the all-walk cubic-degree charge also
fits the same unchanged column reserve. -/
theorem recovery_squared_all_walks_reserve (hs : ParameterRules x p) (V D : ℕ)
    (hV : V + 1 ≤ p.Uocc) (hD : D ≤ p.Dmax) :
    (2 ^ (4 * p.k) * (V + 1) ^ (3 * D)) ^ 2 ≤ 2 ^ (x.n - p.k) := by
  calc
    (2 ^ (4 * p.k) * (V + 1) ^ (3 * D)) ^ 2 =
        2 ^ (8 * p.k) * (V + 1) ^ (6 * D) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      exact congrArg₂ (fun a b : ℕ => 2 ^ a * (V + 1) ^ b) (by omega) (by omega)
    _ ≤ 2 ^ (8 * p.k) * (V + 1) ^ (50 * D) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ _ := hs.recovery_compiler_reserve V D hV hD

end NearQuarticWires.Cells.ParameterRules
