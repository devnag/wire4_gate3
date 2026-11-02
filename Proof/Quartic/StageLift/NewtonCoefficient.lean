import Proof.Quartic.Mask.Polynomial
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open scoped BigOperators

/-- `lem:maskpoly`, paper/paper.tex: subtraction
of exponents equals multiplication of the two parity signs. -/
theorem paritySign_sub (a i : ℕ) (hi : i ≤ a) :
    (-1 : ℤ) ^ (a - i) = (-1 : ℤ) ^ a * (-1 : ℤ) ^ i := by
  have hmul : (-1 : ℤ) ^ (a - i) * (-1 : ℤ) ^ i = (-1 : ℤ) ^ a := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have hsquare : (-1 : ℤ) ^ i * (-1 : ℤ) ^ i = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (-1 : ℤ) ^ (a - i) = (-1 : ℤ) ^ (a - i) *
        ((-1 : ℤ) ^ i * (-1 : ℤ) ^ i) := by rw [hsquare, mul_one]
    _ = (-1 : ℤ) ^ a * (-1 : ℤ) ^ i := by rw [← mul_assoc, hmul]

/-- `lem:maskpoly`, paper/paper.tex: every positive
Newton index is a single signed binomial coefficient, rather than an
unbounded finite-difference computation. -/
theorem newtonCoeff_positive_closed (tau a : ℕ) (ha : 0 < a) :
    Mask.newtonCoeff tau a = (-1 : ℤ) ^ (a - min a tau) *
      ((a - 1).choose (min a tau) : ℤ) := by
  rw [Mask.newtonCoeff_eq_sum_min]
  have hfactor : (∑ i ∈ Finset.range (min a tau + 1),
      (-1 : ℤ) ^ (a - i) * (a.choose i : ℤ)) =
      (-1 : ℤ) ^ a * (∑ i ∈ Finset.range (min a tau + 1),
        (-1 : ℤ) ^ i * (a.choose i : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≤ a := (show i ≤ min a tau by simpa using hi).trans (min_le_left _ _)
    rw [paritySign_sub a i hia]
    ring
  rw [hfactor]
  have hchoose := Int.alternating_sum_range_choose_eq_choose
    (n := a - 1) (m := min a tau)
  have ha' : a - 1 + 1 = a := by omega
  rw [ha'] at hchoose
  rw [hchoose, paritySign_sub a (min a tau) (min_le_left _ _)]
  ring

/-- `lem:maskpoly`, paper/paper.tex: the complete
coefficient-generation branch uses only a zero case, a cutoff test,
and one exact binomial with its parity sign. -/
theorem newtonCoeff_closed (tau a : ℕ) :
    Mask.newtonCoeff tau a =
      if a = 0 then 1 else if a ≤ tau then 0 else
        (-1 : ℤ) ^ (a - tau) * ((a - 1).choose tau : ℤ) := by
  by_cases ha : a = 0
  · subst a
    simp [Mask.newtonCoeff, Mask.cutoff]
  · rw [if_neg ha, newtonCoeff_positive_closed tau a (by omega)]
    by_cases hat : a ≤ tau
    · rw [if_pos hat, min_eq_left hat, Nat.sub_self]
      simp [Nat.choose_eq_zero_of_lt (show a - 1 < a by omega)]
    · rw [if_neg hat, min_eq_right (by omega : tau ≤ a)]

end NearQuarticWires.StageLift
