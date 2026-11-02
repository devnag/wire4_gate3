import Mathlib
set_option autoImplicit false
namespace NearQuarticWires.Cycle
open Finset ZMod

/-- Paper `lem:cycle`: unnormalized cyclic-character orthogonality. -/
theorem sum_mul_character {p : ℕ} [NeZero p] (v : ZMod p) :
    (∑ θ : ZMod p, (stdAddChar (N := p)) (θ * v)) =
      if v = 0 then (p : ℂ) else 0 := by
  classical
  by_cases hv : v = 0
  · simp [hv, ZMod.card]
  · rw [if_neg hv]
    have hne : (stdAddChar (N := p)).mulShift v ≠ 1 := isPrimitive_stdAddChar p hv
    have h := AddChar.sum_eq_zero_of_ne_one hne
    simpa only [AddChar.mulShift_apply, mul_comm] using h

/-- Paper `lem:cycle`: the two concrete walk-score frequency sums factor. -/
theorem two_score_character_sum {p q : ℕ} [NeZero p] [NeZero q]
    (v : ZMod p) (w : ZMod q) :
    (∑ θ : ZMod p, ∑ η : ZMod q,
      (stdAddChar (N := p)) (θ*v) * (stdAddChar (N := q)) (η*w)) =
      (p : ℂ) * (q : ℂ) * (if v = 0 then 1 else 0) * (if w = 0 then 1 else 0) := by
  classical
  rw [← Finset.sum_mul_sum, sum_mul_character, sum_mul_character]
  split_ifs <;> simp_all

#print axioms two_score_character_sum
end NearQuarticWires.Cycle
