import Proof.Quartic.Cells.ParametersGuards
import Proof.Quartic.Algorithm.Parameters

set_option autoImplicit false

namespace NearQuarticWires.Cells.ParameterArithmetic

/-- `sec:params`, paper/paper.tex: the bounded list
search and the bounded least-natural search select the same least lift exponent. -/
theorem algorithm_primeExponent_eq (BN P e : ℕ) (hP : 4 ≤ P)
    (he : liftExponent BN P = some e) : Algorithm.primeExponent BN P = e := by
  let B := max 1 BN
  have hB : LiftPass BN P B := by
    refine ⟨le_max_left _ _, ?_⟩
    calc
      2 ^ (BN + B) ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by dsimp [B]; omega)
      _ = 4 ^ B := by rw [pow_mul]; norm_num
      _ ≤ P ^ B := Nat.pow_le_pow_left hP _
  have hs := liftExponent_spec BN P e he
  have heb : e ≤ B := by
    by_contra hn
    exact hs.2.2 B (by omega) hB
  have hf : (List.range (B + 1)).find? (fun t => decide (LiftPass BN P t)) = some e := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hs.1, e, ?_, ?_, ?_⟩
    · simp only [List.length_range]
      omega
    · simp only [List.getElem_range]
    · intro j hj
      have hn := hs.2.2 j hj
      simp only [List.getElem_range]
      simp [hn]
  unfold Algorithm.primeExponent
  change ((List.range (B + 1)).find? (fun t => decide (LiftPass BN P t))).getD B = e
  rw [hf]
  rfl

/-- `sec:params`, paper/paper.tex: the base-sixteen
ceiling logarithm equals the algorithm's rounded quarter of the base-two one. -/
theorem algorithm_sampleExponent_eq (y : ℚ) :
    ceilLog 16 y = (Nat.clog 2 ⌈y⌉₊ + 3) / 4 := by
  unfold ceilLog
  have h := Nat.clog_pow_left 2 4 ⌈y⌉₊
  norm_num only [Nat.reducePow, Nat.reduceSub] at h
  exact h

end NearQuarticWires.Cells.ParameterArithmetic
