import Proof.Quartic.StagePrep.CensusGate

/-!
# The encoded size bounds the physical wire census

Paper: `def:class`, paper/paper.tex, and
`prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Dispatch

/-- The gate's input and top wire charges of `def:class`,
paper/paper.tex. -/
def gateChargeSum {n : ℕ} (gs : List (NormalizedThresholdGate n)) : ℕ :=
  (gs.map fun g => Transfer.fanIn g + 1).sum

/-- An occurrence's literal gate word pays for its input positions
and top wire in `def:class`, paper/paper.tex. -/
theorem arity_add_one_le_gateWord {n : ℕ} (g : NormalizedThresholdGate n) :
    n + 1 ≤ (gateWord g).length := by
  have hw := length_le_flatMap (List.ofFn g.weight) intWord intWord_len_pos
  have ht := intWord_len_pos g.threshold
  simp only [List.length_ofFn] at hw
  simp only [gateWord, listWord, List.length_append]
  omega

/-- Every occurrence charge is paid by its literal word in
`def:class`, paper/paper.tex. -/
theorem gate_charge_le_word {n : ℕ} (g : NormalizedThresholdGate n) :
    Transfer.fanIn g + 1 ≤ (gateWord g).length := by
  have hf : Transfer.fanIn g ≤ n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact (Nat.add_le_add_right hf _).trans (arity_add_one_le_gateWord g)

/-- Summing occurrence charges preserves the encoded bound of
`def:class`, paper/paper.tex. -/
theorem gateChargeSum_le_wordlength {n : ℕ} (gs : List (NormalizedThresholdGate n)) :
    gateChargeSum gs ≤ (gs.flatMap gateWord).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := gate_charge_le_word g
    simp only [gateChargeSum, List.map_cons, List.sum_cons,
      List.flatMap_cons, List.length_append] at *
    omega

/-- One additional occurrence adds its actual wire charge in
`def:class`, paper/paper.tex. -/
theorem gateChargeSum_take_succ {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (k : ℕ) (hk : k < gs.length) :
    gateChargeSum (gs.take (k + 1)) =
      gateChargeSum (gs.take k) + (Transfer.fanIn gs[k] + 1) := by
  change ((gs.take (k + 1)).map fun g => Transfer.fanIn g + 1).sum = _
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [gateChargeSum, Option.toList, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, Nat.add_zero]

/-- At the next occurrence, the earlier wire charges and the
next full arity fit in the original encoded gate list of
`def:class`, paper/paper.tex. -/
theorem gate_prefix_arity_bound {n : ℕ} (gs : List (NormalizedThresholdGate n))
    (k : ℕ) (hk : k < gs.length) :
    gateChargeSum (gs.take k) + (n + 1) ≤ (gs.flatMap gateWord).length := by
  have hcharge := gateChargeSum_le_wordlength (gs.take k)
  have harity := arity_add_one_le_gateWord gs[k]
  have hpart : ((gs.take (k + 1)).flatMap gateWord).length ≤
      (gs.flatMap gateWord).length := by
    have heq := congrArg (fun xs => (xs.flatMap gateWord).length)
      (List.take_append_drop (k + 1) gs)
    simp only [List.flatMap_append, List.length_append] at heq
    omega
  rw [flatMap_take_len gs gateWord k hk] at hpart
  omega

end NearQuarticWires.StagePrep
