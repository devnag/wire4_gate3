import Proof.Quartic.Cells.ParametersOutputCapacityRounding
import Proof.Quartic.StageOutput.Semantics

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Dispatch
open StageOutput

/-- Outward natural quotient rounding does not increase the
undivided magnitude, Step 5, `prop:sound`, paper/paper.tex. -/
theorem output_ceilQuot_le (n d : ℕ) : ceilQuot n d ≤ n := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [ceilQuot]
  · apply Nat.le_of_lt_succ
    unfold ceilQuot
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    have hmul : n ≤ n * d := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hd
    have hsub : n + d - 1 < n + d := Nat.sub_lt (by omega) (by omega)
    nlinarith only [hmul, hsub]

/-- Both directed natural quotients have the undivided magnitude
bound, Step 5, `prop:sound`, paper/paper.tex. -/
theorem output_quotientMagnitude_le (up : Bool) (n d : ℕ) : quotientMagnitude up n d ≤ n := by
  cases up
  · exact Nat.div_le_self _ _
  · exact output_ceilQuot_le n d

/-- Signed endpoint rounding fits the sum of its two natural
parts, Step 5, `prop:sound`, paper/paper.tex. -/
theorem output_differenceRound_natAbs_le (up : Bool) (x y d : ℕ) :
    (differenceRound up x y d).natAbs ≤ x + y := by
  unfold differenceRound
  split_ifs
  · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using
      (output_quotientMagnitude_le (!up) (y - x) d).trans ((Nat.sub_le y x).trans (Nat.le_add_left y x))
  · simpa only [Int.natAbs_natCast] using
      (output_quotientMagnitude_le up (x - y) d).trans ((Nat.sub_le x y).trans (Nat.le_add_right x y))

/-- Both actual signed rounded endpoints fit a common binary
height from the scalar codec, Step 5, `sec:algorithm`, paper/paper.tex. -/
theorem output_rounded_magnitude_bounds (d : Input) (B W : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hn : d.n ≤ B) (hk : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ W) (hs : d.Stored env)
    (hpowerN : env powerN = 2 ^ d.n) (hpowerK : env powerK = 2 ^ d.k)
    (hD : env roundD = d.denominator) :
    d.floorValue.natAbs ≤ 2 ^ (28 * (B + 1) + 1) ∧
      d.ceilValue.natAbs ≤ 2 ^ (28 * (B + 1) + 1) := by
  have hl := output_basic_expression_leaves d B env hf hk hs hpowerK
  have hu := output_upper_expression_leaves d B env hf hn hk hs hpowerN hpowerK hD
  have hv := output_basic_expression_values d env hs hpowerK
  have hLP := (output_numerator_expression_capacity lowerPositiveExpr B W env hw (by decide) hl.2.1).1
  have hLN := (output_numerator_expression_capacity lowerNegativeExpr B W env hw (by decide) hl.2.2.1).1
  have hUP := (output_numerator_expression_capacity upperPositiveExpr B W env hw (by decide) hu).1
  have hUN := (output_numerator_expression_capacity upperNegativeExpr B W env hw (by decide) hl.2.2.2).1
  rw [hv.2.1] at hLP
  rw [hv.2.2.1] at hLN
  rw [hv.2.2.2] at hUN
  rw [output_upper_expression_value d env hs hpowerN hpowerK hD] at hUP
  constructor
  · calc
      d.floorValue.natAbs ≤ d.lowerPositive + d.lowerNegative := output_differenceRound_natAbs_le false _ _ _
      _ ≤ 2 ^ (28 * (B + 1)) + 2 ^ (28 * (B + 1)) := Nat.add_le_add hLP hLN
      _ = _ := by rw [pow_succ]; omega
  · calc
      d.ceilValue.natAbs ≤ d.upperPositive + d.upperNegative := output_differenceRound_natAbs_le true _ _ _
      _ ≤ 2 ^ (28 * (B + 1)) + 2 ^ (28 * (B + 1)) := Nat.add_le_add hUP hUN
      _ = _ := by rw [pow_succ]; omega

/-- The center and radius additions and the two canonical rational
printers fit the charged width, Step 5 and `prop:time`,
paper/paper.tex. -/
theorem output_printing_capacity (d : Input) (B W : ℕ) (env : Fin VV → ℕ)
    (hf : ∀ xv ∈ d.fields, xv.2 < 2 ^ B) (hn : d.n ≤ B) (hk : d.k ≤ B)
    (hw : 64 * (B + 1) ≤ W) (hs : d.Stored env)
    (hpowerN : env powerN = 2 ^ d.n) (hpowerK : env powerK = 2 ^ d.k)
    (hD : env roundD = d.denominator) :
    d.floorValue.natAbs + d.ceilValue.natAbs + 2 ^ (d.n + 1) + 2 < 2 ^ W ∧
      d.centerNumerator ≤ 2 ^ (28 * (B + 1) + 2) ∧
      d.radiusNumerator ≤ 2 ^ (28 * (B + 1) + 2) ∧
      2 ^ (d.n + 1) ≤ 2 ^ (28 * (B + 1) + 2) ∧
      2 * 2 ^ (28 * (B + 1) + 2) ≤ 2 ^ W := by
  have hmag := output_rounded_magnitude_bounds d B W env hf hn hk hw hs hpowerN hpowerK hD
  have hp : 2 ^ (d.n + 1) ≤ (2 : ℕ) ^ (28 * (B + 1) + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have htwo : 2 ≤ (2 : ℕ) ^ (28 * (B + 1) + 1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
      (by omega : 1 ≤ 28 * (B + 1) + 1)
  have hsum : d.floorValue.natAbs + d.ceilValue.natAbs ≤ 2 ^ (28 * (B + 1) + 2) := by
    rw [show 28 * (B + 1) + 2 = (28 * (B + 1) + 1) + 1 by omega, pow_succ]
    omega
  refine ⟨?_, (Int.natAbs_add_le _ _).trans hsum, (Int.natAbs_sub_le _ _).trans ?_,
    hp.trans (Nat.pow_le_pow_right (by norm_num) (by omega)), ?_⟩
  · calc
      d.floorValue.natAbs + d.ceilValue.natAbs + 2 ^ (d.n + 1) + 2 ≤
          4 * 2 ^ (28 * (B + 1) + 1) := by omega
      _ = 2 ^ (28 * (B + 1) + 3) := by
        rw [show 28 * (B + 1) + 3 = (28 * (B + 1) + 1) + 2 by omega, pow_add]
        norm_num
        ring
      _ < 2 ^ W := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · simpa only [Nat.add_comm] using hsum
  · calc
      2 * 2 ^ (28 * (B + 1) + 2) = 2 ^ (28 * (B + 1) + 3) := by
        calc
          2 * 2 ^ (28 * (B + 1) + 2) = 2 ^ (28 * (B + 1) + 2) * 2 := Nat.mul_comm _ _
          _ = 2 ^ ((28 * (B + 1) + 2) + 1) := (pow_succ _ _).symm
          _ = _ := by congr 1
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)

end NearQuarticWires.Cells
