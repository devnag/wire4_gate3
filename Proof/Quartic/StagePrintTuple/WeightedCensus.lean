import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open scoped BigOperators

/-- `lem:print` and `prop:time`, paper/paper.tex: distinct supports of bounded degree are counted by their
actual cardinality, with one child-color factor for each chosen variable. -/
theorem weighted_support_sum_le (V D b : ℕ) (keys : Finset (Finset (Fin V)))
    (hD : ∀ S ∈ keys, S.card ≤ D) :
    ∑ S ∈ keys, b ^ S.card ≤ (1 + V * b) ^ D := by
  have hf : ∀ S ∈ keys, S.card ∈ Finset.range (D + 1) := by
    intro S hS
    exact Finset.mem_range.mpr (by have := hD S hS; omega)
  rw [← Finset.sum_fiberwise_of_maps_to' hf (fun j => b ^ j)]
  calc
    ∑ j ∈ Finset.range (D + 1), ∑ _S ∈ keys with _S.card = j, b ^ j ≤
        ∑ j ∈ Finset.range (D + 1), D.choose j * (V * b) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjD : j ≤ D := by have := Finset.mem_range.mp hj; omega
      have hc : (keys.filter (fun S => S.card = j)).card ≤ V.choose j := by
        have hsub : keys.filter (fun S => S.card = j) ⊆
            (Finset.univ : Finset (Fin V)).powersetCard j := by
          intro S hS
          exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hS).2⟩
        simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card hsub
      have hchoose : 1 ≤ D.choose j := Nat.choose_pos hjD
      calc
        ∑ _S ∈ keys with _S.card = j, b ^ j = (keys.filter (fun S => S.card = j)).card * b ^ j := by simp
        _ ≤ V.choose j * b ^ j := Nat.mul_le_mul_right _ hc
        _ ≤ V ^ j * b ^ j := Nat.mul_le_mul_right _ (Nat.choose_le_pow V j)
        _ = (V * b) ^ j := (Nat.mul_pow _ _ _).symm
        _ ≤ D.choose j * (V * b) ^ j := by simpa using Nat.mul_le_mul_right ((V * b) ^ j) hchoose
    _ = (1 + V * b) ^ D := by
      rw [add_comm 1, add_pow]
      apply Finset.sum_congr rfl
      intro j _
      simp [Nat.mul_comm]

/-- `prop:time`, paper/paper.tex: the weighted
original-child square census fits the unchanged sharp exponent2D,
without multiplying a maximum term census by a maximum child census. -/
theorem weighted_squared_child_sum_le (V D mc : ℕ) (keys : Finset (Finset (Fin V)))
    (hD : ∀ S ∈ keys, S.card ≤ D) :
    ∑ S ∈ keys, mc ^ (2 * S.card) ≤ (1 + V * mc) ^ (2 * D) := by
  have hb : 1 + V * mc ^ 2 ≤ (1 + V * mc) ^ 2 := by
    have hV := Nat.mul_le_mul_right (mc ^ 2) (Nat.le_mul_self V)
    calc
      1 + V * mc ^ 2 ≤ 1 + V * V * mc ^ 2 := Nat.add_le_add_left hV 1
      _ ≤ 1 + V * V * mc ^ 2 + 2 * (V * mc) := Nat.le_add_right _ _
      _ = (1 + V * mc) ^ 2 := by ring
  calc
    ∑ S ∈ keys, mc ^ (2 * S.card) = ∑ S ∈ keys, (mc ^ 2) ^ S.card := by
      apply Finset.sum_congr rfl
      intro S _
      rw [pow_mul]
    _ ≤ (1 + V * mc ^ 2) ^ D := weighted_support_sum_le V D (mc ^ 2) keys hD
    _ ≤ ((1 + V * mc) ^ 2) ^ D := Nat.pow_le_pow_left hb D
    _ = (1 + V * mc) ^ (2 * D) := (pow_mul _ _ _).symm

end NearQuarticWires.StageTuple
