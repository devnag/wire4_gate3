import Proof.Quartic.Walks.Core
import Proof.Gates.RationalRateChain

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators
open NearCubicGates.PublicSamplingRates NearCubicGates.NestedRateChain

/-- Paper `imp:chain`/`lem:localize`, paper/paper.tex: the integer
multiplier in the ACTUAL public accelerated rate chain. -/
noncomputable def chainFactor (T h ell : ℝ) (r : ℕ) : ℤ :=
  factor (rateRatio (initialRatio T h ell) r)

/-- Paper `lem:localize`, paper/paper.tex: its literal final integer error,
with the public denominator and rate product, not assumed reconstruction data. -/
noncomputable def finalError (T h ell : ℝ) (K : ℕ → ℤ) (Y : ℤ) (J : ℕ) : ℤ :=
  (denominator T h ell : ℤ) * K J - (product (initialRatio T h ell) J : ℤ) * Y

/-- Paper `lem:localize`, paper/paper.tex: the initial digit bound after
scaling the ACTUAL nested-rate deviation by the walk length `2m`. -/
theorem first_walk_digit_bound (T h ell : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (m : ℕ) (K : ℕ → ℤ) (Y : ℤ)
    (hY : |(Y : ℝ)| ≤ (2 * m : ℕ) * liveCap T h ell)
    (hstage : |(K 0 : ℝ) - rate T h ell 0 * (Y : ℝ)| ≤
      (2 * m : ℕ) * fluctuation T h ell (rate T h ell 0)) :
    |(K 0 : ℝ)| ≤ (m : ℝ) * h := by
  have hp := (all_rates_bounded T h ell hT hh 0).1
  have hb := initial_digit_bound T h ell hT hh
  calc
    _ = |((K 0 : ℝ) - rate T h ell 0 * (Y : ℝ)) +
      rate T h ell 0 * (Y : ℝ)| := by congr 1; ring
    _ ≤ |(K 0 : ℝ) - rate T h ell 0 * (Y : ℝ)| +
      |rate T h ell 0 * (Y : ℝ)| := abs_add_le _ _
    _ ≤ (2 * m : ℕ) * fluctuation T h ell (rate T h ell 0) +
        rate T h ell 0 * ((2 * m : ℕ) * liveCap T h ell) := by
      rw [abs_mul, abs_of_pos hp]
      exact add_le_add hstage (mul_le_mul_of_nonneg_left hY hp.le)
    _ ≤ (m : ℝ) * h := by
      have hb' := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (2 * m : ℕ) by positivity)
      push_cast at hb' ⊢
      nlinarith

/-- Paper `lem:localize`, paper/paper.tex: arbitrary successive proposed
sample values have a short correction digit whenever the two true stage
deviations satisfy the scaled Bernstein event. -/
theorem correction_walk_digit_bound (T h ell : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (m : ℕ) (K : ℕ → ℤ) (Y : ℤ) (r : ℕ)
    (hactive : rateRatio (initialRatio T h ell) r < 1 / 256)
    (hfirst : |(K r : ℝ) - rate T h ell r * (Y : ℝ)| ≤
      (2 * m : ℕ) * fluctuation T h ell (rate T h ell r))
    (hnext : |(K (r + 1) : ℝ) - rate T h ell (r + 1) * (Y : ℝ)| ≤
      (2 * m : ℕ) * fluctuation T h ell (rate T h ell (r + 1))) :
    |((K (r + 1) - chainFactor T h ell r * K r : ℤ) : ℝ)| ≤ (m : ℝ) * h := by
  let a : ℝ := factor (rateRatio (initialRatio T h ell) r)
  have ha : 0 ≤ a := by positivity
  have hid : ((K (r + 1) - chainFactor T h ell r * K r : ℤ) : ℝ) =
      ((K (r + 1) : ℝ) - rate T h ell (r + 1) * (Y : ℝ)) -
        a * ((K r : ℝ) - rate T h ell r * (Y : ℝ)) := by
    rw [NearCubicGates.SampledChainMoments.public_rate_recurrence T h ell r hactive]
    simp only [chainFactor, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    dsimp [a]
    ring
  rw [hid]
  calc
    _ ≤ |(K (r + 1) : ℝ) - rate T h ell (r + 1) * (Y : ℝ)| +
      |a * ((K r : ℝ) - rate T h ell r * (Y : ℝ))| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le ((K (r + 1) : ℝ) - rate T h ell (r + 1) * (Y : ℝ))
          (-(a * ((K r : ℝ) - rate T h ell r * (Y : ℝ)))))
    _ ≤ (2 * m : ℕ) * fluctuation T h ell (rate T h ell (r + 1)) +
      a * ((2 * m : ℕ) * fluctuation T h ell (rate T h ell r)) := by
      rw [abs_mul, abs_of_nonneg ha]
      exact add_le_add hnext (mul_le_mul_of_nonneg_left hfirst ha)
    _ ≤ (m : ℝ) * h := by
      have hb := correction_digit_bound T h ell hT hh r hactive
      have hb' := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ (2 * m : ℕ) by positivity)
      dsimp [a] at *
      push_cast at hb' ⊢
      nlinarith

/-- Paper `lem:localize`, paper/paper.tex: the actual final public error
has the precise constant `172m`, after the scaled deviation and stopping test. -/
theorem final_walk_error_bound (T h ell : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (m : ℕ) (K : ℕ → ℤ) (Y : ℤ) (J : ℕ)
    (hstopped : 1 / 256 ≤ rateRatio (initialRatio T h ell) J)
    (hstage : |(K J : ℝ) - rate T h ell J * (Y : ℝ)| ≤
      (2 * m : ℕ) * fluctuation T h ell (rate T h ell J)) :
    |(finalError T h ell K Y J : ℝ)| ≤
      172 * m * (product (initialRatio T h ell) J : ℝ) * T * liveCap T h ell / h := by
  let M : ℝ := denominator T h ell
  let A : ℝ := product (initialRatio T h ell) J
  let pi := rate T h ell J
  let s := fluctuation T h ell pi
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast (denominator_bounds T h ell hT hh).1
  have hpi : 0 < pi := (all_rates_bounded T h ell hT hh J).1
  have hratio : M * pi = A := by
    dsimp [M, pi, A]
    rw [rate_is_rational_product T h ell hT hh J]
    exact mul_div_cancel₀ _ (ne_of_gt hM)
  have hid : (finalError T h ell K Y J : ℝ) = M * ((K J : ℝ) - pi * (Y : ℝ)) := by
    simp only [finalError, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    change M * (K J : ℝ) - A * (Y : ℝ) = _
    rw [← hratio]
    ring
  have hs : s ≤ (86 * T * liveCap T h ell / h) * pi := by
    exact (div_le_iff₀ hpi).mp (terminal_error_bound T h ell hT hh J hstopped)
  have hMs : M * s ≤ A * (86 * T * liveCap T h ell / h) := by
    calc
      _ ≤ M * ((86 * T * liveCap T h ell / h) * pi) :=
        mul_le_mul_of_nonneg_left hs hM.le
      _ = (M * pi) * (86 * T * liveCap T h ell / h) := by ring
      _ = _ := by rw [hratio]
  rw [hid, abs_mul, abs_of_pos hM]
  calc
    _ ≤ M * ((2 * m : ℕ) * s) := mul_le_mul_of_nonneg_left hstage hM.le
    _ ≤ (2 * m : ℕ) * (A * (86 * T * liveCap T h ell / h)) := by
      nlinarith [mul_le_mul_of_nonneg_left hMs
        (show (0 : ℝ) ≤ (2 * m : ℕ) by positivity)]
    _ = _ := by dsimp [A]; push_cast; ring

/-- Paper `lem:localize`, paper/paper.tex: the COMPLETE deterministic
conclusion on the simultaneous stage event, with `mh` digits and `172m` final
error for the literal public rate chain. -/
theorem localize_on_stage_event (T h ell : ℝ) (hT : 0 < T) (hh : 64 * T ≤ h)
    (m : ℕ) (K : ℕ → ℤ) (Y : ℤ) (J : ℕ)
    (hactive : ∀ r, r < J → rateRatio (initialRatio T h ell) r < 1 / 256)
    (hstopped : 1 / 256 ≤ rateRatio (initialRatio T h ell) J)
    (hY : |(Y : ℝ)| ≤ (2 * m : ℕ) * liveCap T h ell)
    (hstage : ∀ r, r ≤ J → |(K r : ℝ) - rate T h ell r * (Y : ℝ)| ≤
      (2 * m : ℕ) * fluctuation T h ell (rate T h ell r)) :
    (∀ r, r ≤ J → |((NearCubicGates.CountingCore.proposedDigit
      (chainFactor T h ell) K r : ℤ) : ℝ)| ≤ (m : ℝ) * h) ∧
    |(finalError T h ell K Y J : ℝ)| ≤
      172 * m * (product (initialRatio T h ell) J : ℝ) * T * liveCap T h ell / h := by
  refine ⟨?_, final_walk_error_bound T h ell hT hh m K Y J hstopped (hstage J le_rfl)⟩
  intro r hr
  cases r with
  | zero => exact first_walk_digit_bound T h ell hT hh m K Y hY (hstage 0 (by omega))
  | succ r =>
      change |((K (r + 1) - chainFactor T h ell r * K r : ℤ) : ℝ)| ≤ (m : ℝ) * h
      exact correction_walk_digit_bound T h ell hT hh m K Y r
        (hactive r (by omega)) (hstage r (by omega)) (hstage (r + 1) hr)

end NearQuarticWires.Walks
