import Proof.Quartic.Cells.ParametersScalarEstimates

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- Coefficients of the scalar-value bounds for `sec:params`,
paper/paper.tex and `prop:time`. -/
def preparationCoefficients (B1 : ℕ) : List ℕ :=
  [1, 16, B1 + 80, B1 + 20, B1 + 20000, 48 * (B1 + 20),
    96 * (B1 + 20) * (B1 + 20000), 33, 2 * B1 + 112, 2 * B1 + 130,
    8 * (2 * B1 + 130), 34, 8, 273, 32 * B1 + 2200, 32 * B1 + 2201,
    512 * (B1 + 20000) + 4, 512 * (B1 + 20000) + 5,
    128 * (B1 + 20000), 4 * (B1 + 20000), 528]

/-- One fixed coefficient dominates every scalar coefficient used in
the preparation bounds of `prop:time`, paper/paper.tex. -/
def preparationCoefficient (B1 : ℕ) : ℕ := (preparationCoefficients B1).sum + 1

/-- A polynomial envelope for scalar parameter values in `sec:params`
and `prop:time`, paper/paper.tex. -/
def preparationEnvelope (B1 n : ℕ) : ℕ := preparationCoefficient B1 * (n + 1) ^ (B1 + 12)

/-- Each nonnegative entry in the coefficient list of the preparation
envelope is at most its sum, `prop:time`, paper/paper.tex. -/
theorem preparation_coefficient_le {B1 a : ℕ} (ha : a ∈ preparationCoefficients B1) :
    a ≤ preparationCoefficient B1 := by
  have hlist : ∀ (values : List ℕ) (v : ℕ), v ∈ values → v ≤ values.sum := by
    intro values
    induction values with
    | nil => simp
    | cons b tail ih =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Nat.le_add_right _ _
      · exact (ih v hv).trans (Nat.le_add_left _ _)
  exact (hlist _ _ ha).trans (Nat.le_add_right _ _)

/-- A scalar bound of any listed coefficient and permitted degree
fits the common preparation envelope, `prop:time`, paper/paper.tex. -/
theorem preparation_envelope_succ (B1 n a degree : ℕ)
    (ha : a ∈ preparationCoefficients B1) (hd : degree ≤ B1 + 12) :
    a * (n + 1) ^ degree ≤ preparationEnvelope B1 n := by
  exact Nat.mul_le_mul (preparation_coefficient_le ha)
    (Nat.pow_le_pow_right (Nat.succ_pos _) hd)

/-- The common preparation envelope also bounds powers of the actual
arity, `prop:time`, paper/paper.tex. -/
theorem preparation_envelope_base (B1 n a degree : ℕ)
    (ha : a ∈ preparationCoefficients B1) (hd : degree ≤ B1 + 12) :
    a * n ^ degree ≤ preparationEnvelope B1 n :=
  (Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.le_succ _) _)).trans
    (preparation_envelope_succ B1 n a degree ha hd)

/-- Positivity and the elementary arity bound of the preparation
envelope, `prop:time`, paper/paper.tex. -/
theorem preparation_envelope_arity (B1 n : ℕ) : n + 1 ≤ preparationEnvelope B1 n := by
  simpa only [one_mul, pow_one] using preparation_envelope_succ B1 n 1 1
    (by simp [preparationCoefficients]) (by omega)

end NearQuarticWires.Cells.ParameterArithmetic
