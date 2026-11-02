import Proof.Quartic.Cells.ParametersArithmetic

/-!
# The integer quotient defining the incidence bound

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

/-- The integer numerator for `U` in `sec:params`,
paper/paper.tex. -/
def uNumerator (r W den : ℕ) : ℕ :=
  9216 * (r * r * r) * (W * W) * (den * den)

/-- The positive integer denominator for `U` in `sec:params`,
paper/paper.tex. -/
def uDenominator (n num : ℕ) : ℕ := (num * num) * (n * n * n)

/-- All numerator products of `sec:params`, paper/paper.tex, are bounded before any later guard is known. -/
theorem uNumerator_parts (r W den : ℕ) (hr : 0 < r) (hW : 0 < W) (hd : 0 < den) :
    9216 ≤ uNumerator r W den ∧
    r * r ≤ uNumerator r W den ∧
    r * r * r ≤ uNumerator r W den ∧
    W * W ≤ uNumerator r W den ∧
    den * den ≤ uNumerator r W den ∧
    9216 * (r * r * r) ≤ uNumerator r W den ∧
    9216 * (r * r * r) * (W * W) ≤ uNumerator r W den := by
  have hr3 : 0 < r * r * r := Nat.mul_pos (Nat.mul_pos hr hr) hr
  have hW2 : 0 < W * W := Nat.mul_pos hW hW
  have hd2 : 0 < den * den := Nat.mul_pos hd hd
  have hpre : 0 < 9216 * (r * r * r) := Nat.mul_pos (by norm_num) hr3
  have hpre2 : 0 < 9216 * (r * r * r) * (W * W) := Nat.mul_pos hpre hW2
  have hp2 : 9216 * (r * r * r) * (W * W) ≤ uNumerator r W den :=
    Nat.le_mul_of_pos_right _ hd2
  have hp : 9216 * (r * r * r) ≤ uNumerator r W den :=
    (Nat.le_mul_of_pos_right _ hW2).trans hp2
  have hrr : r * r * r ≤ uNumerator r W den :=
    (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 9216)).trans hp
  exact ⟨(Nat.le_mul_of_pos_right _ hr3).trans hp,
    (Nat.le_mul_of_pos_right _ hr).trans hrr, hrr,
    (Nat.le_mul_of_pos_left _ hpre).trans hp2,
    Nat.le_mul_of_pos_left _ hpre2, hp, hp2⟩

/-- All denominator products of `sec:params`, paper/paper.tex, are bounded before later parameter guards. -/
theorem uDenominator_parts (n num : ℕ) (hn : 0 < n) (hu : 0 < num) :
    0 < uDenominator n num ∧ num * num ≤ uDenominator n num ∧
    n * n ≤ uDenominator n num ∧ n * n * n ≤ uDenominator n num := by
  have hn3 : 0 < n * n * n := Nat.mul_pos (Nat.mul_pos hn hn) hn
  have hu2 : 0 < num * num := Nat.mul_pos hu hu
  have hncube : n * n * n ≤ uDenominator n num := Nat.le_mul_of_pos_left _ hu2
  exact ⟨Nat.mul_pos hu2 hn3, Nat.le_mul_of_pos_right _ hn3,
    (Nat.le_mul_of_pos_right _ hn).trans hncube, hncube⟩

/-- The exact radius encoding gives the integer quotient for
`U` in `sec:params`, paper/paper.tex. -/
theorem u_ratio_encoding (n r W num den : ℕ) (beta : ℚ)
    (hnum : beta.num = num) (hden : beta.den = den)
    (hn : 0 < n) (hu : 0 < num) (hd : 0 < den) :
    (96 ^ 2 * (r : ℚ) ^ 3 * (W : ℚ) ^ 2) /
        (beta ^ 2 * (n : ℚ) ^ 3) =
      ((uNumerator r W den : ℕ) : ℚ) / uDenominator n num := by
  have hb : beta = (num : ℚ) / den := by
    have h := Rat.num_div_den beta
    rw [hnum, hden] at h
    simpa only [Int.cast_natCast] using h.symm
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hu0 : (num : ℚ) ≠ 0 := by exact_mod_cast hu.ne'
  have hd0 : (den : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [hb]
  unfold uNumerator uDenominator
  push_cast
  field_simp
  ring

end NearQuarticWires.StagePrep
