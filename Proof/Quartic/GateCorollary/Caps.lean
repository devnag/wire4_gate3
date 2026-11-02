import Proof.Quartic.Statement.Joint

set_option autoImplicit false

namespace NearQuarticWires.GateCorollary

open NearCubicGates.Target NearQuarticWires.Statement

/-- `cor:gates`, paper/paper.tex: multiplication
by the n+1 possible wires per charged copy respects the exact two
natural-number floor caps. Zero denominators give zero caps. -/
theorem gateCap_wires_le (K n : ℕ) (hn : 1 ≤ n) :
    (n + 1) * gateCap K n ≤ wireCap K n := by
  let L : ℝ := (lambda n : ℝ) ^ ((17 : ℝ) / 4)
  let M : ℝ := (mu n : ℝ) ^ ((15 : ℝ) / 2)
  let D : ℝ := (K : ℝ) * L * M
  have hg : gateCap K n = ⌊(n : ℝ) ^ 3 / (2 * D)⌋₊ := by
    unfold gateCap
    congr 1
    congr 1
    dsimp [D, L, M]
    ring
  have hw : wireCap K n = ⌊(n : ℝ) ^ 4 / D⌋₊ := rfl
  rw [hg, hw]
  by_cases hz : D = 0
  · simp [hz]
  have hD0 : 0 ≤ D := by dsimp [D, L, M]; positivity
  have hD : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hz)
  have hq : 0 ≤ (n : ℝ) ^ 3 / (2 * D) := by positivity
  have hf : (⌊(n : ℝ) ^ 3 / (2 * D)⌋₊ : ℝ) ≤ (n : ℝ) ^ 3 / (2 * D) :=
    Nat.floor_le hq
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have htwo : (n : ℝ) + 1 ≤ 2 * n := by linarith
  rw [Nat.le_floor_iff (show 0 ≤ (n : ℝ) ^ 4 / D by positivity)]
  push_cast
  calc
    ((n : ℝ) + 1) * (⌊(n : ℝ) ^ 3 / (2 * D)⌋₊ : ℝ)
        ≤ ((n : ℝ) + 1) * ((n : ℝ) ^ 3 / (2 * D)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ ≤ (2 * n) * ((n : ℝ) ^ 3 / (2 * D)) := mul_le_mul_of_nonneg_right htwo hq
    _ = (n : ℝ) ^ 4 / D := by field_simp

end NearQuarticWires.GateCorollary
