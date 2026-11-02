import Proof.Quartic.Cells.Mixed

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires Finset
open NearCubicWires.WireExponent3_5.Shared

/-- `sec:cells`, paper/paper.tex: indexing list occurrences retains every repeated gate. -/
theorem population_eq_sum_fin (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) :
    population P gates c u v = ∑ i : Fin gates.length, (delta P gates[i] c u v).natAbs := by
  exact (Fin.sum_univ_fun_getElem gates (fun g => (delta P g c u v).natAbs)).symm

/-- `sec:cells`, paper/paper.tex: the walk-facing integer population is the sum of absolute residuals. -/
theorem population_cast_eq_sum_abs (P : StarParams) (gates : List (NormalizedThresholdGate P.n))
    (c : BitInput P.n) (u v : P.Errors) :
    (population P gates c u v : ℤ) = ∑ i : Fin gates.length, |delta P gates[i] c u v| := by
  rw [population_eq_sum_fin]
  simp only [Nat.cast_sum, Int.natCast_natAbs]

/-- `sec:imports-star`, paper/paper.tex: at most one flipped coordinate comes from each side's block. -/
theorem flipSet_card_le (P : StarParams) (side : Fin (P.r / 2) → Fin P.r) (e : P.Errors) :
    (P.flipSet side e).card ≤ P.r / 2 := by
  classical
  let blocks : Fin (P.r / 2) → Finset (Fin P.n) := fun j =>
    (e j).toFinset.image (P.blockCoord (side j))
  have hs : P.flipSet side e ⊆ univ.biUnion blocks := by
    intro x hx
    obtain ⟨j, i, he, rfl⟩ := (P.mem_flipSet side e x).mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    simp [blocks, he]
  have hb : ∀ j, (blocks j).card ≤ 1 := by
    intro j
    unfold blocks
    cases e j <;> simp
  calc (P.flipSet side e).card ≤ (univ.biUnion blocks).card := Finset.card_le_card hs
    _ ≤ ∑ j, (blocks j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin (P.r / 2), 1 := Finset.sum_le_sum fun j _ => hb j
    _ = P.r / 2 := by simp

end NearQuarticWires.Cells
