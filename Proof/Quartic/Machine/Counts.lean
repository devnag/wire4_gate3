import Mathlib

set_option autoImplicit false

namespace NearQuarticWires.Machine

/-- `sec:cycle`, paper/paper.tex: one closed walk retains all `m` row
and all `m` column vertices, including repeated vertices. -/
abbrev ClosedWalk (m N : ℕ) := (Fin m → Fin N) × (Fin m → Fin N)

/-- `cor:conditional`, paper/paper.tex: at each of the `2m` edge
positions choose the constant term or one of the `Q` occurrence labels. -/
abbrev GammaChoice (m Q : ℕ) := Fin (2 * m) → Fin (Q + 1)

/-- `sec:cycle`, paper/paper.tex: the concrete closed-walk type has
exactly `N^(2m)` elements.  No distinct-vertex condition is imposed. -/
theorem closedWalk_card (m N : ℕ) :
    Fintype.card (ClosedWalk m N) = N ^ (2 * m) := by
  simp [ClosedWalk, ← pow_add, two_mul]

/-- `sec:cycle`, paper/paper.tex, and `prop:time`, paper/paper.tex:
for `k = 2*kh` the walk enumeration has exactly `2^(m*k)` entries. -/
theorem closedWalk_card_two_pow (m kh : ℕ) :
    Fintype.card (ClosedWalk m (2 ^ kh)) = 2 ^ (m * (2 * kh)) := by
  rw [closedWalk_card, ← pow_mul]
  congr 1
  ring

/-- `cor:conditional`, paper/paper.tex, and `prop:time`: occurrence-preserving expansion has `(Q+1)^(2m)` choices. -/
theorem gammaChoice_card (m Q : ℕ) :
    Fintype.card (GammaChoice m Q) = (Q + 1) ^ (2 * m) := by
  simp [GammaChoice]

/-- `prop:time`, paper/paper.tex: the `m=4` walk/Gamma expansion
cost is part of `2^(10k + O(lambda))`, provided the independently proved
sample-exponent estimate is supplied.  This counts the loop iterations;
it is not a proof of the machine's per-iteration arithmetic cost. -/
theorem walkGammaPolynomialCost_le (n k q cQ lam c Q : ℕ)
    (hQ : Q ≤ 2 ^ q) (hq : 4 * q ≤ 3 * k + 4 * cQ * lam)
    (hn : n + 1 ≤ 2 ^ (lam + 1)) :
    2 ^ (4 * k) * (Q + 1) ^ 8 * (n + 1) ^ c ≤
      2 ^ (10 * k + (8 * cQ + c) * lam + 8 + c) := by
  have hQ1 : Q + 1 ≤ 2 ^ (q + 1) := by
    have hp : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  calc
    2 ^ (4 * k) * (Q + 1) ^ 8 * (n + 1) ^ c ≤
        2 ^ (4 * k) * (2 ^ (q + 1)) ^ 8 * (2 ^ (lam + 1)) ^ c :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ1 8))
        (Nat.pow_le_pow_left hn c)
    _ = 2 ^ (4 * k + (q + 1) * 8 + (lam + 1) * c) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ (10 * k + (8 * cQ + c) * lam + 8 + c) := by
      apply Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      nlinarith

end NearQuarticWires.Machine
