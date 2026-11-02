import Proof.Quartic.StageMainPopulation.Request

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicGates.Close.Interfaces
open StageCert

/-- `def:mask` and witness (W2), paper/paper.tex: consecutive original banks use consecutive actual witness
indices, retaining exact magnitudes and every repeated occurrence. -/
theorem populationPrefix_append {n : ℕ} (xs ys : List (NormalizedThresholdGate n))
    (points : Fin 4 → ℕ) (bits : List Bool) (index : ℕ) :
    populationPrefix (xs ++ ys) points bits index (xs.length + ys.length) =
      populationPrefix xs points bits index xs.length +
        populationPrefix ys points bits (index + xs.length) ys.length := by
  have hfirst : populationPrefix (xs ++ ys) points bits index xs.length =
      populationPrefix xs points bits index xs.length := by
    unfold populationPrefix
    congr 1
    apply List.map_congr_left
    intro k hk
    have hx : k < xs.length := List.mem_range.mp hk
    have hxy : k < (xs ++ ys).length := by simp only [List.length_append]; omega
    simp only [dif_pos hx, dif_pos hxy, List.getElem_append_left hx]
  have htail : ∀ k, k ≤ ys.length →
      populationPrefix (xs ++ ys) points bits index (xs.length + k) =
        populationPrefix xs points bits index xs.length +
          populationPrefix ys points bits (index + xs.length) k := by
    intro k
    induction k with
    | zero => intro _; simpa [populationPrefix] using hfirst
    | succ k ih =>
      intro hk
      have hy : k < ys.length := by omega
      have hxy : xs.length + k < (xs ++ ys).length := by simp only [List.length_append]; omega
      rw [show xs.length + (k + 1) = (xs.length + k) + 1 by omega,
        populationPrefix_succ, ih (by omega), populationPrefix_succ, dif_pos hy, dif_pos hxy]
      simp only [List.getElem_append_right (by omega : xs.length ≤ xs.length + k),
        Nat.add_sub_cancel_left, Nat.add_assoc]
  exact htail ys.length le_rfl

end NearQuarticWires.StageMainPopulation
