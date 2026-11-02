import Proof.Quartic.StageMain.Weight

/-!
# Exact prefix sums in threshold evaluation

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. A list of signed weights is consumed in
coordinate order. The positive and negative prefix sums are bounded by the
sum of absolute weights, and the packed coordinate word is divided by two
after each consumed weight.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch

def positiveScore : List ℤ → ℕ → ℕ
  | [], _ => 0
  | w :: ws, x => positiveContribution w x + positiveScore ws (x / 2)

def negativeScore : List ℤ → ℕ → ℕ
  | [], _ => 0
  | w :: ws, x => negativeContribution w x + negativeScore ws (x / 2)

theorem contribution_bounds (w : ℤ) (x : ℕ) :
    positiveContribution w x ≤ w.natAbs ∧ negativeContribution w x ≤ w.natAbs := by
  unfold positiveContribution negativeContribution
  split_ifs <;> cases w <;> simp

theorem score_bounds (ws : List ℤ) (x : ℕ) :
    positiveScore ws x ≤ (ws.map Int.natAbs).sum ∧ negativeScore ws x ≤ (ws.map Int.natAbs).sum := by
  induction ws generalizing x with
  | nil => simp [positiveScore, negativeScore]
  | cons w ws ih =>
    have hc := contribution_bounds w x
    have hh := ih (x / 2)
    simp only [positiveScore, negativeScore, List.map_cons, List.sum_cons]
    constructor <;> omega

theorem score_append (ws vs : List ℤ) (x : ℕ) :
    positiveScore (ws ++ vs) x = positiveScore ws x + positiveScore vs (x / 2 ^ ws.length) ∧
    negativeScore (ws ++ vs) x = negativeScore ws x + negativeScore vs (x / 2 ^ ws.length) := by
  induction ws generalizing x with
  | nil => simp [positiveScore, negativeScore]
  | cons w ws ih =>
    have hh := ih (x / 2)
    simp only [List.cons_append, positiveScore, negativeScore, List.length_cons]
    rw [hh.1, hh.2]
    have he : x / 2 / 2 ^ ws.length = x / 2 ^ (ws.length + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    simp only [he, Nat.add_assoc, and_self]

theorem score_take_succ (ws : List ℤ) (k : ℕ) (hk : k < ws.length) (x : ℕ) :
    positiveScore (ws.take (k + 1)) x = positiveScore (ws.take k) x + positiveContribution ws[k] (x / 2 ^ k) ∧
    negativeScore (ws.take (k + 1)) x = negativeScore (ws.take k) x + negativeContribution ws[k] (x / 2 ^ k) := by
  rw [List.take_succ_eq_append_getElem hk]
  have hh := score_append (ws.take k) [ws[k]] x
  simpa only [List.length_take, Nat.min_eq_left hk.le, positiveScore, negativeScore, Nat.add_zero] using hh

end NearQuarticWires.StageMain
