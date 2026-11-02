import Proof.Quartic.StagePrep.IntegerCensus
import Proof.Quartic.Transfer.Counter4

/-!
# The integer list census and actual wire count

Paper: `def:class`, paper/paper.tex. The arithmetic
below uses physical occurrences and nonzero input weights.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicWires NearCubicGates.Close.Interfaces

/-- The nonzero-weight census of `def:class`, paper/paper.tex, on a list of signed integers. -/
def wireSum (ws : List ℤ) : ℕ := (ws.map wireBit).sum

/-- The empty census in `def:class`, paper/paper.tex. -/
theorem wireSum_nil : wireSum [] = 0 := rfl

/-- The census is additive over actual weight lists in `def:class`,
paper/paper.tex. -/
theorem wireSum_append (xs ys : List ℤ) :
    wireSum (xs ++ ys) = wireSum xs + wireSum ys := by
  simp [wireSum]

/-- The census of `def:class`, paper/paper.tex, is
bounded by the number of encoded input weights. -/
theorem wireSum_le_length (ws : List ℤ) : wireSum ws ≤ ws.length := by
  induction ws with
  | nil => rfl
  | cons z ws ih =>
    have hz : wireBit z ≤ 1 := by unfold wireBit; split_ifs <;> omega
    simp only [wireSum, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- An additional list entry gives the exact next wire charge in
`def:class`, paper/paper.tex. -/
theorem wireSum_take_succ (ws : List ℤ) (k : ℕ) (hk : k < ws.length) :
    wireSum (ws.take (k + 1)) = wireSum (ws.take k) + wireBit ws[k] := by
  change ((ws.take (k + 1)).map wireBit).sum = ((ws.take k).map wireBit).sum + wireBit ws[k]
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The list census equals the actual gate fan-in of `def:class`,
paper/paper.tex, including zero input weights. -/
theorem fanIn_eq_wireSum {n : ℕ} (g : NormalizedThresholdGate n) :
    Transfer.fanIn g = wireSum (List.ofFn g.weight) := by
  classical
  rw [Transfer.fanIn, Finset.card_filter]
  simp only [wireSum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g.weight i = 0
  · simp [wireBit, h]
  · simp [wireBit, h]

end NearQuarticWires.StagePrep
