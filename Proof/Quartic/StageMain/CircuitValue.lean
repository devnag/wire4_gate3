import Proof.Quartic.StageMain.ThresholdValue
import Proof.Gates.Dispatch.WitnessA
import Proof.Gates.Interfaces.Counter

/-!
# Signed top scores from packed bottom-gate values

Paper: `def:class`, paper/paper.tex. The top score is the
literal weighted sum of bottom-gate bits. Packing the bits in occurrence
order and consuming them alongside the signed coefficients gives that
same integer, including zero coefficients and empty lists.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires
open NearCubicGates.Close.Counter NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

theorem score_zero (ws : List ℤ) : positiveScore ws 0 = 0 ∧ negativeScore ws 0 = 0 := by
  induction ws with
  | nil => simp [positiveScore, negativeScore]
  | cons w ws ih =>
    simp [positiveScore, negativeScore, positiveContribution, negativeContribution, ih]

theorem score_bits (ws : List ℤ) (bs : List Bool) :
    (positiveScore ws (bitsValue bs) : ℤ) - negativeScore ws (bitsValue bs) =
      ((bs.zip ws).map fun bw => bw.2 * if bw.1 then 1 else 0).sum := by
  induction ws generalizing bs with
  | nil => simp [positiveScore, negativeScore]
  | cons w ws ih =>
    cases bs with
    | nil => simp [bitsValue, score_zero]
    | cons b bs =>
      have hd : bitsValue (b :: bs) / 2 = bitsValue bs := by
        simpa using bitsValue_div (b :: bs) 1
      have hm : (bitsValue (b :: bs)).testBit 0 = b := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        simp only [pow_zero, Nat.div_one]
        have hh := bitsValue_div_mod (b :: bs) 0
        simp only [pow_zero, Nat.div_one, List.getD_cons_zero] at hh
        rw [hh]
        cases b <;> decide
      have hc := contribution_difference w (bitsValue (b :: bs))
      rw [hm] at hc
      have hi := ih bs
      simp only [positiveScore, negativeScore, hd, Nat.cast_add,
        List.zip_cons_cons, List.map_cons, List.sum_cons]
      omega

theorem circuit_score_bits {n : ℕ} (C : NCircuit n) (x : BitInput n) :
    (positiveScore C.coeffs (bitsValue (C.gates.map fun g => g.eval x)) : ℤ) -
      negativeScore C.coeffs (bitsValue (C.gates.map fun g => g.eval x)) = C.score x := by
  rw [score_bits]
  unfold NCircuit.score
  congr 1
  have hm (gs : List (NormalizedThresholdGate n)) (zs : List ℤ) :
      ((gs.map fun g => g.eval x).zip zs).map (fun bw => bw.2 * if bw.1 then (1 : ℤ) else 0) =
        (gs.zip zs).map (fun gc => gc.2 * if gc.1.eval x then (1 : ℤ) else 0) := by
    induction gs generalizing zs with
    | nil => simp
    | cons g gs ih =>
      cases zs with
      | nil => simp
      | cons z zs =>
        simp only [List.map_cons, List.zip_cons_cons]
        congr 1
        exact ih zs
  exact hm C.gates C.coeffs

/-- The natural table index is the encoded signed score plus its offset. -/
theorem circuit_index_bits {n : ℕ} (C : NCircuit n) (x : BitInput n) :
    (C.score x + C.topWeight).toNat =
      (positiveScore C.coeffs (bitsValue (C.gates.map fun g => g.eval x)) + C.topWeight) -
        negativeScore C.coeffs (bitsValue (C.gates.map fun g => g.eval x)) := by
  have hs := circuit_score_bits C x
  omega

end NearQuarticWires.StageMain
