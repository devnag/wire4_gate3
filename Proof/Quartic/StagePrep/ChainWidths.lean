import Proof.Quartic.StagePrep.ChainInitial

/-!
# Word widths for the finite rational rate chain

Paper: `imp:chain`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch

/-- The integer loops for `imp:chain`, `lem:selector`, paper/paper.tex, fit the fixed word size from the initial exact ratio
and the public height, including a later failed stopping test. -/
theorem chain_width_bounds (S D h J L Wd : ℕ)
    (hD : D < 2 ^ (5 * S + 22)) (hh : h < 2 ^ S)
    (hJ : J < 2 ^ S) (hL : L < 2 ^ S) (hW : 6 * S + 40 ≤ Wd) :
    1024 * D + (h + 33) * (h + 33) + J + 1000 < 2 ^ Wd ∧
    L * D + 2 < 2 ^ Wd ∧ J + 1 < 2 ^ Wd := by
  have hh33 : (h + 33) * (h + 33) < 2 ^ (2 * S + 12) := by
    have hp : h + 33 < 2 ^ (S + 6) := by
      have heq : (2 : ℕ) ^ (S + 6) = 64 * 2 ^ S := by ring
      have hpos : 1 ≤ 2 ^ S := Nat.one_le_two_pow
      omega
    rw [show 2 * S + 12 = (S + 6) + (S + 6) by ring]
    exact lt_pow_mul hp hp
  have e1 : 1024 * D < 2 ^ (5 * S + 32) := by
    have heq : (2 : ℕ) ^ (5 * S + 32) = 1024 * 2 ^ (5 * S + 22) := by ring
    omega
  have e2 : (h + 33) * (h + 33) < 2 ^ (5 * S + 32) :=
    lt_pow_mono hh33 (by omega)
  have e3 : J + 1000 < 2 ^ (5 * S + 32) := by
    have h1000 : 1000 < 2 ^ 10 := by norm_num
    refine lt_of_lt_of_le (Nat.add_lt_add hJ h1000) ?_
    have h1 : 2 ^ S ≤ 2 ^ (5 * S + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 10 ≤ 2 ^ (5 * S + 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2 : ℕ) ^ (5 * S + 32) = 4 * 2 ^ (5 * S + 30) := by ring
    omega
  have e4 : (2 : ℕ) ^ (5 * S + 32) * 4 ≤ 2 ^ Wd := by
    rw [show (2 : ℕ) ^ (5 * S + 32) * 4 = 2 ^ (5 * S + 34) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLD : L * D < 2 ^ (6 * S + 22) := by
    have hp := lt_pow_mul hL hD
    simpa only [show S + (5 * S + 22) = 6 * S + 22 by omega] using hp
  have hLDW : 2 ^ (6 * S + 22) * 4 ≤ 2 ^ Wd := by
    rw [show (2 : ℕ) ^ (6 * S + 22) * 4 = 2 ^ (6 * S + 24) by ring]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp : 1 ≤ 2 ^ (6 * S + 22) := Nat.one_le_two_pow
  have hJ2 : J + 1 < 2 ^ (S + 1) := by
    have hpS : 1 ≤ 2 ^ S := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  exact ⟨by omega, by omega, lt_pow_mono hJ2 (by omega)⟩

end NearQuarticWires.StagePrep
