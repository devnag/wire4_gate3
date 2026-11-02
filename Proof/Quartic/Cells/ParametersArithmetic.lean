import Proof.Gates.Counter.Params
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

open NearCubicGates.Close.Counter

/-- `sec:params`, paper/paper.tex: the least natural square-root
upper bound, computed with integer arithmetic. -/
def ceilSqrt (a : ℕ) : ℕ :=
  if (Nat.sqrt a) ^ 2 = a then Nat.sqrt a else Nat.sqrt a + 1

/-- `sec:params`, paper/paper.tex: the selected root passes
the exact integer-power comparison. -/
theorem le_ceilSqrt_sq (a : ℕ) : a ≤ ceilSqrt a ^ 2 := by
  unfold ceilSqrt
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt' a).le

/-- `sec:params`, paper/paper.tex: exact minimality of the
integer square-root upper bound used for `Xmax` and `MF`. -/
theorem ceilSqrt_le_iff (a t : ℕ) : ceilSqrt a ≤ t ↔ a ≤ t ^ 2 := by
  constructor
  · intro ht
    have ha := le_ceilSqrt_sq a
    nlinarith
  · intro ha
    by_cases he : a = t ^ 2
    · subst a
      simp [ceilSqrt, Nat.sqrt_eq']
    · have hlt : Nat.sqrt a < t := Nat.sqrt_lt'.mpr (lt_of_le_of_ne ha he)
      unfold ceilSqrt
      split_ifs <;> omega

/-- `sec:params`, paper/paper.tex: rational square-root ceilings
are reduced to the natural ceiling followed by an integer square root. -/
def ceilSqrtRat (x : ℚ) : ℕ := ceilSqrt ⌈x⌉₊

/-- `sec:params`, paper/paper.tex: the rational square-root
ceiling is exactly the least natural passing the squared comparison. -/
theorem ceilSqrtRat_le_iff (x : ℚ) (t : ℕ) :
    ceilSqrtRat x ≤ t ↔ x ≤ (t : ℚ) ^ 2 := by
  rw [ceilSqrtRat, ceilSqrt_le_iff, Nat.ceil_le]
  norm_cast

/-- `sec:params`, paper/paper.tex: the squared rational value
is below the square of the selected integer. -/
theorem le_ceilSqrtRat_sq (x : ℚ) : x ≤ (ceilSqrtRat x : ℚ) ^ 2 :=
  (ceilSqrtRat_le_iff x _).mp le_rfl

/-- `sec:params`, paper/paper.tex: exact ceiling logarithm
of a rational value, without a real-valued logarithm computation. -/
def ceilLog (base : ℕ) (x : ℚ) : ℕ := Nat.clog base ⌈x⌉₊

/-- `sec:params`, paper/paper.tex: the rational ceiling
logarithm is the least exponent passing the power comparison. -/
theorem ceilLog_le_iff {base : ℕ} (hb : 1 < base) (x : ℚ) (t : ℕ) :
    ceilLog base x ≤ t ↔ x ≤ ((base ^ t : ℕ) : ℚ) := by
  rw [ceilLog, Nat.clog_le_iff_le_pow hb, Nat.ceil_le]

/-- `sec:params`, paper/paper.tex: the chosen exponent passes
the rational power comparison. -/
theorem le_pow_ceilLog {base : ℕ} (hb : 1 < base) (x : ℚ) :
    x ≤ ((base ^ ceilLog base x : ℕ) : ℚ) :=
  (ceilLog_le_iff hb x _).mp le_rfl

/-- `sec:params`, paper/paper.tex: the concentration exponent
is required to be positive. -/
def positiveLog2 (x : ℚ) : ℕ := max 1 (ceilLog 2 x)

/-- `sec:params`, paper/paper.tex: exact least-positive
selection of the concentration exponent. -/
theorem positiveLog2_le_iff (x : ℚ) (t : ℕ) :
    positiveLog2 x ≤ t ↔ 1 ≤ t ∧ x ≤ ((2 ^ t : ℕ) : ℚ) := by
  rw [positiveLog2, max_le_iff, ceilLog_le_iff (by norm_num : 1 < 2)]

/-- `sec:params`, paper/paper.tex: `T` is computed from
the literal concentration numerator. -/
def concentrationT (m k J : ℕ) (beta : ℚ) : ℕ :=
  positiveLog2 (((2 ^ (m * k + 2 * m + 5) * J : ℕ) : ℚ) / beta)

/-- `sec:params`, paper/paper.tex: `T` is exactly the least
positive integer with `2^T beta ≥ 2^(mk+2m+5) J`. -/
theorem concentrationT_le_iff (m k J : ℕ) {beta : ℚ} (hb : 0 < beta) (t : ℕ) :
    concentrationT m k J beta ≤ t ↔
      1 ≤ t ∧ ((2 ^ (m * k + 2 * m + 5) * J : ℕ) : ℚ) ≤ 2 ^ t * beta := by
  rw [concentrationT, positiveLog2_le_iff, div_le_iff₀ hb]
  norm_cast

/-- `sec:params`, paper/paper.tex: the dyadic sample size
is obtained by a base-sixteen ceiling logarithm of the fourth-power test. -/
def sampleExponent (N m I : ℕ) (eta : ℚ) : ℕ :=
  ceilLog 16 ((((1024 * N * m : ℕ) : ℚ) ^ 4 * (4 * N ^ 2 * I : ℕ)) / eta ^ 8)

/-- `sec:params`, paper/paper.tex: least dyadic sample size
with the paper's raised fourth-power inequality. -/
theorem sampleExponent_le_iff (N m I : ℕ) {eta : ℚ} (he : 0 < eta) (q : ℕ) :
    sampleExponent N m I eta ≤ q ↔
      ((1024 * N * m : ℕ) : ℚ) ^ 4 * (4 * N ^ 2 * I : ℕ) ≤
        (((2 ^ q : ℕ) : ℚ) ^ 4) * eta ^ 8 := by
  have he8 : 0 < eta ^ 8 := pow_pos he _
  have hp : ((16 ^ q : ℕ) : ℚ) = (((2 ^ q : ℕ) : ℚ) ^ 4) := by
    push_cast
    rw [← pow_mul, mul_comm q 4, pow_mul]
    norm_num
  rw [sampleExponent, ceilLog_le_iff (by norm_num : 1 < 16), div_le_iff₀ he8, hp]

/-- `sec:params`, paper/paper.tex: the lifted prime-power
condition is an exact integer comparison, including positivity of its exponent. -/
def LiftPass (BN P e : ℕ) : Prop := 1 ≤ e ∧ 2 ^ (BN + e) ≤ P ^ e

instance (BN P : ℕ) : DecidablePred (LiftPass BN P) := fun e => by
  unfold LiftPass
  infer_instance

/-- `sec:params`, paper/paper.tex: bounded exact selection
of the least positive lift exponent. -/
def liftExponent (BN P : ℕ) : Option ℕ := leastUpTo (LiftPass BN P) (BN + 1)

/-- `sec:params`, paper/paper.tex: every permitted prime
scale has a lift exponent within the explicit search bound. -/
theorem lift_search_bound (BN P : ℕ) (hP : 4 ≤ P) : LiftPass BN P (BN + 1) := by
  refine ⟨by omega, ?_⟩
  calc
    2 ^ (BN + (BN + 1)) ≤ 2 ^ (2 * (BN + 1)) := by gcongr <;> omega
    _ = 4 ^ (BN + 1) := by rw [pow_mul]; norm_num
    _ ≤ P ^ (BN + 1) := Nat.pow_le_pow_left hP _

/-- `sec:params`, paper/paper.tex: the lift search succeeds
at every permitted scale. -/
theorem liftExponent_isSome (BN P : ℕ) (hP : 4 ≤ P) :
    ∃ e, liftExponent BN P = some e :=
  leastUpTo_isSome _ _ _ le_rfl (lift_search_bound BN P hP)

/-- `sec:params`, paper/paper.tex: successful selection
supplies the exact power inequality and leastness. -/
theorem liftExponent_spec (BN P e : ℕ) (h : liftExponent BN P = some e) :
    LiftPass BN P e ∧ e ≤ BN + 1 ∧ ∀ t, t < e → ¬ LiftPass BN P t :=
  leastUpTo_spec _ _ _ h

/-- `sec:params`, paper/paper.tex: every prime strictly
above half the chosen scale lifts strictly past the signed numerator bound. -/
theorem prime_pow_gt (BN P e p : ℕ) (he : LiftPass BN P e) (hp : P < 2 * p) :
    2 ^ BN < p ^ e := by
  have hepos : 0 < e := by have := he.1; omega
  have hpow : P ^ e < (2 * p) ^ e := by
    exact Nat.pow_lt_pow_left hp (by omega)
  have hmul : 2 ^ e * 2 ^ BN < 2 ^ e * p ^ e := by
    calc
      2 ^ e * 2 ^ BN = 2 ^ (BN + e) := by rw [pow_add]; exact Nat.mul_comm _ _
      _ ≤ P ^ e := he.2
      _ < (2 * p) ^ e := hpow
      _ = 2 ^ e * p ^ e := mul_pow _ _ _
  exact (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ e)).mp hmul

end NearQuarticWires.Cells.ParameterArithmetic
