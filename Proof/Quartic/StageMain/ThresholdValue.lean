import Proof.Quartic.StageMain.ScoreList
import Proof.MachineModel.CanonicalSignedGateEvaluationProgram

/-!
# The packed-point score and inclusive threshold convention

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. Subtracting the two nonnegative
accumulators gives the literal integer score. Comparing it to the signed
threshold uses the inclusive `≥` convention, including zero-dimensional
gates and exact ties.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires

/-- The input point represented by a low-bit-first natural number. -/
def packedPoint (n x : ℕ) : BitInput n := fun i => x.testBit i.val

theorem contribution_difference (w : ℤ) (x : ℕ) :
    (positiveContribution w x : ℤ) - negativeContribution w x =
      w * (if x.testBit 0 then 1 else 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [pow_zero, Nat.div_one, decide_eq_true_eq]
  unfold positiveContribution negativeContribution
  split_ifs <;> cases w <;> simp
  omega

theorem score_difference {n : ℕ} (weights : Fin n → ℤ) (x : ℕ) :
    (positiveScore (List.ofFn weights) x : ℤ) - negativeScore (List.ofFn weights) x =
      ∑ i : Fin n, weights i * (if packedPoint n x i then 1 else 0) := by
  induction n generalizing x with
  | zero => simp [positiveScore, negativeScore]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [positiveScore, negativeScore, Nat.cast_add]
    rw [Fin.sum_univ_succ]
    have hh := ih (fun i => weights i.succ) (x / 2)
    have hc := contribution_difference (weights 0) x
    have htail : (∑ i : Fin n, weights i.succ * (if packedPoint n (x / 2) i then (1 : ℤ) else 0)) =
        ∑ i : Fin n, weights i.succ * (if packedPoint (n + 1) x i.succ then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [packedPoint, Fin.val_succ, Nat.testBit_div_two]
      rfl
    rw [htail] at hh
    change _ = weights 0 * (if x.testBit 0 then 1 else 0) + _
    omega

/-- The natural comparison of the two signed score parts is the gate bit. -/
theorem gate_eval_packed {n : ℕ} (g : NormalizedThresholdGate n) (x : ℕ) :
    g.eval (packedPoint n x) =
      decide (negativeScore (List.ofFn g.weight) x + g.threshold.toNat ≤
        positiveScore (List.ofFn g.weight) x + (-g.threshold).toNat) := by
  unfold NormalizedThresholdGate.eval
  have hs := score_difference g.weight x
  apply decide_eq_decide.mpr
  rw [← hs]
  omega

end NearQuarticWires.StageMain
