import Proof.Quartic.Cells.ParametersBounds
import Proof.Gates.Counter.Eventual
import Proof.Gates.Transfer.Budget

set_option autoImplicit false

namespace NearQuarticWires.Cells.CoreRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: positivity of the
two integer logarithmic scales at every selected input. -/
theorem logarithms_pos (hs : CoreRules x p) : 2 ≤ p.lambda ∧ 1 ≤ p.mu := by
  rw [hs.lambda_eq, hs.mu_eq]
  exact ⟨NearCubicGates.Close.Transfer.lambda_ge_two hs.input_valid.1,
    NearCubicGates.Close.Transfer.mu_ge_one hs.input_valid.1⟩

/-- `lem:asymptotics`, paper/paper.tex: the second
logarithmic scale is bounded by the first. -/
theorem mu_le_lambda (hs : CoreRules x p) : p.mu ≤ p.lambda := by
  rw [hs.mu_eq, hs.lambda_eq]
  exact NearCubicGates.Close.Counter.clog_le_self _

/-- `lem:asymptotics`, paper/paper.tex: the exact child
count is at most eight times `n² lambda`. -/
theorem childCap_le (hs : CoreRules x p) : p.childCap ≤ 8 * x.n ^ 2 * p.lambda := by
  have hn : 4 ≤ x.n := hs.input_valid.1
  have hl := hs.logarithms_pos.1
  have hc : Nat.clog 2 (x.n + 1) ≤ p.lambda + 1 := by
    rw [hs.lambda_eq]
    exact Cells.clog_succ_le x.n
  have hb : NearCubicGates.Close.Counter.B0 x.n ≤ 4 * x.n * (p.lambda + 1) := by
    unfold NearCubicGates.Close.Counter.B0
    exact Nat.mul_le_mul_left _ hc
  have h4 : 4 * x.n ≤ 2 * x.n * p.lambda := by nlinarith
  have hsmall : p.lambda + 3 ≤ 2 * x.n * p.lambda := by nlinarith
  have hsum : NearCubicGates.Close.Counter.B0 x.n + p.lambda + 3 ≤
      8 * x.n * p.lambda := by nlinarith
  calc
    p.childCap = x.n * (NearCubicGates.Close.Counter.B0 x.n + p.lambda + 3) := by
      rw [hs.childCap_eq]
      unfold Cells.childCap
      rw [hs.lambda_eq]
      rfl
    _ ≤ x.n * (8 * x.n * p.lambda) := Nat.mul_le_mul_left _ hsum
    _ = 8 * x.n ^ 2 * p.lambda := by ring

/-- `lem:asymptotics`, paper/paper.tex: the actual
occurrence factor has polynomial bound `273 n⁶ lambda`. -/
theorem Uocc_polynomial (hs : CoreRules x p) :
    p.Uocc ≤ 273 * x.n ^ 6 * p.lambda := by
  have ha : p.NatAtoms = 34 * x.n ^ 4 := by rw [hs.NatAtoms_eq, hs.m_eq]; ring
  have hn := hs.n_pos
  have hl := hs.logarithms_pos.1
  calc
    p.Uocc = 1 + p.NatAtoms * p.childCap := hs.Uocc_eq
    _ ≤ 1 + (34 * x.n ^ 4) * (8 * x.n ^ 2 * p.lambda) := by
      rw [ha]
      gcongr
      exact hs.childCap_le
    _ = 1 + 272 * x.n ^ 6 * p.lambda := by ring
    _ ≤ 273 * x.n ^ 6 * p.lambda := by
      have hp : 0 < x.n ^ 6 * p.lambda := by positivity
      nlinarith

/-- `lem:asymptotics`, paper/paper.tex: the occurrence
factor fits the explicit binary exponent `6 lambda + mu + 9`. -/
theorem Uocc_binary (hs : CoreRules x p) :
    p.Uocc ≤ 2 ^ (6 * p.lambda + p.mu + 9) := by
  have hn : x.n ≤ 2 ^ p.lambda := by
    rw [hs.lambda_eq]
    exact Nat.le_pow_clog (by norm_num) _
  have hl : p.lambda ≤ 2 ^ p.mu := by
    rw [hs.lambda_eq, hs.mu_eq]
    exact Nat.le_pow_clog (by norm_num) _
  calc
    p.Uocc ≤ 273 * x.n ^ 6 * p.lambda := hs.Uocc_polynomial
    _ ≤ 512 * (2 ^ p.lambda) ^ 6 * 2 ^ p.mu := by gcongr; norm_num
    _ = 2 ^ (9 + p.lambda * 6 + p.mu) := by
      rw [show (512 : ℕ) = 2 ^ 9 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
    _ = 2 ^ (6 * p.lambda + p.mu + 9) := by congr 1; omega

/-- `lem:asymptotics`, paper/paper.tex: the exact printing
logarithm has leading coefficient six in the input logarithm. -/
theorem clog_Uocc_le (hs : CoreRules x p) :
    Nat.clog 2 p.Uocc ≤ 6 * p.lambda + p.mu + 9 :=
  Nat.clog_le_of_le_pow hs.Uocc_binary

/-- `lem:asymptotics`, paper/paper.tex: the occurrence
factor is at least the input length. -/
theorem n_le_Uocc (hs : CoreRules x p) : x.n ≤ p.Uocc := by
  have hc : x.n ≤ p.childCap := by
    rw [hs.childCap_eq]
    unfold Cells.childCap
    nlinarith
  have ha : 0 < p.NatAtoms := by
    rw [hs.NatAtoms_eq]
    have hn := hs.n_pos
    positivity
  rw [hs.Uocc_eq]
  nlinarith

/-- `lem:asymptotics`, paper/paper.tex: two explicit
linear bounds for the occurrence logarithm. -/
theorem clog_Uocc_bounds (hs : CoreRules x p) :
    p.lambda ≤ Nat.clog 2 p.Uocc ∧ Nat.clog 2 p.Uocc ≤ 12 * p.lambda := by
  constructor
  · rw [hs.lambda_eq]
    exact Nat.clog_mono_right 2 hs.n_le_Uocc
  · have := hs.clog_Uocc_le
    have := hs.mu_le_lambda
    have := hs.logarithms_pos.1
    omega

end NearQuarticWires.Cells.CoreRules

namespace NearQuarticWires.Cells.ParameterRules

open ParameterArithmetic

variable {x : ParameterInput} {p : Parameters}

/-- `lem:asymptotics`, paper/paper.tex: positivity of the
two integer logarithmic scales at every selected input. -/
theorem logarithms_pos (hs : ParameterRules x p) : 2 ≤ p.lambda ∧ 1 ≤ p.mu :=
  CoreRules.logarithms_pos (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the second
logarithmic scale is bounded by the first. -/
theorem mu_le_lambda (hs : ParameterRules x p) : p.mu ≤ p.lambda :=
  CoreRules.mu_le_lambda (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the exact child
count is at most eight times `n² lambda`. -/
theorem childCap_le (hs : ParameterRules x p) : p.childCap ≤ 8 * x.n ^ 2 * p.lambda :=
  CoreRules.childCap_le (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the actual
occurrence factor has polynomial bound `273 n⁶ lambda`. -/
theorem Uocc_polynomial (hs : ParameterRules x p) :
    p.Uocc ≤ 273 * x.n ^ 6 * p.lambda :=
  CoreRules.Uocc_polynomial (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the occurrence
factor fits the explicit binary exponent `6 lambda + mu + 9`. -/
theorem Uocc_binary (hs : ParameterRules x p) :
    p.Uocc ≤ 2 ^ (6 * p.lambda + p.mu + 9) :=
  CoreRules.Uocc_binary (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the exact printing
logarithm has leading coefficient six in the input logarithm. -/
theorem clog_Uocc_le (hs : ParameterRules x p) :
    Nat.clog 2 p.Uocc ≤ 6 * p.lambda + p.mu + 9 :=
  CoreRules.clog_Uocc_le (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: the occurrence
factor is at least the input length. -/
theorem n_le_Uocc (hs : ParameterRules x p) : x.n ≤ p.Uocc :=
  CoreRules.n_le_Uocc (hs : CoreRules x p)

/-- `lem:asymptotics`, paper/paper.tex: two explicit
linear bounds for the occurrence logarithm. -/
theorem clog_Uocc_bounds (hs : ParameterRules x p) :
    p.lambda ≤ Nat.clog 2 p.Uocc ∧ Nat.clog 2 p.Uocc ≤ 12 * p.lambda :=
  CoreRules.clog_Uocc_bounds (hs : CoreRules x p)

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: a degree passes exactly when it is below an explicit quotient. -/
theorem degreePass_iff (hs : ParameterRules x p) (D : ℕ) :
    DegreePass x.n p.m p.k p.Uocc D ↔
      D ≤ ((x.n - p.k) / 100 - (p.m * p.k + 2)) / Nat.clog 2 p.Uocc := by
  have hz := hs.initial_degree
  unfold DegreePass at hz ⊢
  have hlog : 0 < Nat.clog 2 p.Uocc := by
    have := hs.clog_Uocc_bounds.1
    have := hs.logarithms_pos.1
    omega
  rw [Nat.le_div_iff_mul_le hlog]
  have hzero : p.m * p.k + 2 ≤ (x.n - p.k) / 100 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (100 : ℕ))).mpr
    nlinarith
  constructor
  · intro hD
    have ht : p.m * p.k + 2 + D * Nat.clog 2 p.Uocc ≤ (x.n - p.k) / 100 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (100 : ℕ))).mpr
      nlinarith
    omega
  · intro hD
    have ht : p.m * p.k + 2 + D * Nat.clog 2 p.Uocc ≤ (x.n - p.k) / 100 := by omega
    have he := (Nat.le_div_iff_mul_le (by norm_num : 0 < (100 : ℕ))).mp ht
    nlinarith

/-- `sec:params` and `lem:asymptotics`, paper/paper.tex: the maximal degree is exactly the indicated integer quotient. -/
theorem Dmax_quotient (hs : ParameterRules x p) :
    p.Dmax = ((x.n - p.k) / 100 - (p.m * p.k + 2)) / Nat.clog 2 p.Uocc := by
  apply le_antisymm
  · exact (hs.degreePass_iff p.Dmax).mp hs.degree_maximal.1
  · apply hs.degree_maximal.2
    exact (hs.degreePass_iff _).mpr le_rfl

end NearQuarticWires.Cells.ParameterRules

