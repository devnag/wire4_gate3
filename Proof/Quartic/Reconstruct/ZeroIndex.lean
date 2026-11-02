import Proof.Quartic.Reconstruct.BoxArith

/-!
# The position of the point `0` in a box

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (`v = H̃(0)`).

The tag of a system carries the position of the point `0` in its list of points (`Phases.systemTag`). When the two
coordinate lists are intervals `lo'_j - B_j, …` with `len_j` points (`BoxArith.boxAxisOf_eq`), this position is
`(B_1 - lo'_1) len_2 + (B_2 - lo'_2)` if `lo'_j ≤ B_j < lo'_j + len_j` for both coordinates, and the number of points
`len_1 len_2` otherwise (`idxOf_zero_box`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

/-- The position of `x` in the interval `c, c + 1, …, c + n - 1`. -/
theorem idxOf_range_add (c x : ℤ) : ∀ n : ℕ, ((List.range n).map fun i : ℕ => c + (i : ℤ)).idxOf x =
    if c ≤ x ∧ x < c + n then (x - c).toNat else n
  | 0 => by
    simp only [List.range_zero, List.map_nil, Nat.cast_zero, add_zero]
    split_ifs with h
    · omega
    · rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.idxOf_append, idxOf_range_add c x n]
    have hmem : x ∈ (List.range n).map (fun i : ℕ => c + (i : ℤ)) ↔ c ≤ x ∧ x < c + n := by
      simp only [List.mem_map, List.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        omega
      · rintro ⟨h1, h2⟩
        exact ⟨(x - c).toNat, by omega, by omega⟩
    by_cases h : c ≤ x ∧ x < c + n
    · rw [if_pos (hmem.mpr h), if_pos h, if_pos (by omega)]
    · rw [if_neg (fun h' => h (hmem.mp h'))]
      simp only [List.map_cons, List.map_nil, List.length_map, List.length_range]
      by_cases hx : x = c + n
      · subst hx
        rw [if_pos (by omega)]
        simp
      · rw [if_neg (by omega), List.idxOf_cons_ne _ (fun e => hx e.symm)]
        simp
        omega

/-- **The position of the point `0` in the points of a box.** -/
theorem idxOf_zero_box (lo0 B0 lo1 B1 : ℕ) (n0 n1 : ℕ) :
    ((((List.range n0).map fun i : ℕ => ((lo0 : ℕ) : ℤ) - B0 + (i : ℤ)) ×ˢ
        ((List.range n1).map fun i : ℕ => ((lo1 : ℕ) : ℤ) - B1 + (i : ℤ))).map pairList).idxOf [0, 0] =
      if lo0 ≤ B0 ∧ B0 < lo0 + n0 ∧ lo1 ≤ B1 ∧ B1 < lo1 + n1 then (B0 - lo0) * n1 + (B1 - lo1) else n0 * n1 := by
  set L1 := (List.range n1).map fun i : ℕ => ((lo1 : ℕ) : ℤ) - B1 + (i : ℤ) with hL1
  have hL1len : L1.length = n1 := by simp [hL1]
  have hrow : ∀ a : ℤ, ((L1.map (Prod.mk a)).map pairList).idxOf [0, 0] =
      if a = 0 ∧ lo1 ≤ B1 ∧ B1 < lo1 + n1 then B1 - lo1 else n1 := by
    intro a
    rw [List.map_map]
    by_cases ha : a = 0
    · subst ha
      have hf : ((L1.map (pairList ∘ Prod.mk 0))) = L1.map (fun b => [0, b]) := rfl
      rw [hf]
      have hinj : ∀ l : List ℤ, (l.map fun b => [(0 : ℤ), b]).idxOf [0, 0] = l.idxOf 0 := by
        intro l
        induction l with
        | nil => rfl
        | cons b l ih =>
          by_cases hb : b = 0
          · subst hb; simp
          · rw [List.map_cons, List.idxOf_cons_ne _ (by simp [hb]), List.idxOf_cons_ne _ hb, ih]
      rw [hinj, hL1, idxOf_range_add]
      by_cases hc : lo1 ≤ B1 ∧ B1 < lo1 + n1
      · rw [if_pos (by omega), if_pos ⟨rfl, hc⟩]
        omega
      · rw [if_neg (by omega), if_neg (fun h => hc h.2)]
    · rw [if_neg (fun h => ha h.1), List.idxOf_eq_length]
      · simp [hL1]
      · simp only [List.mem_map, Function.comp, pairList, not_exists, not_and]
        intro b _ h
        exact ha (List.cons.inj h).1
  induction n0 with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.nil_product, List.idxOf_nil]
    split_ifs <;> omega
  | succ n ih =>
    have hprod : ((List.range (n + 1)).map fun i : ℕ => ((lo0 : ℕ) : ℤ) - B0 + (i : ℤ)) ×ˢ L1 =
        (((List.range n).map fun i : ℕ => ((lo0 : ℕ) : ℤ) - B0 + (i : ℤ)) ×ˢ L1) ++
          L1.map (Prod.mk (((lo0 : ℕ) : ℤ) - B0 + (n : ℤ))) := by
      rw [List.range_succ, List.map_append]
      simp [SProd.sprod, List.product, List.flatMap_append]
    rw [hprod, List.map_append, List.idxOf_append, ih, hrow]
    have hlen : ((((List.range n).map fun i : ℕ => ((lo0 : ℕ) : ℤ) - B0 + (i : ℤ)) ×ˢ L1).map pairList).length =
        n * n1 := by simp [List.length_product, hL1len]
    have hmem : [0, 0] ∈ (((List.range n).map fun i : ℕ => ((lo0 : ℕ) : ℤ) - B0 + (i : ℤ)) ×ˢ L1).map pairList ↔
        lo0 ≤ B0 ∧ B0 < lo0 + n ∧ lo1 ≤ B1 ∧ B1 < lo1 + n1 := by
      simp only [List.mem_map, List.mem_product, List.mem_range, Prod.exists, pairList, hL1]
      constructor
      · rintro ⟨a, b, ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩, h⟩
        simp only [List.cons.injEq, and_true] at h
        omega
      · rintro ⟨h1, h2, h3, h4⟩
        exact ⟨0, 0, ⟨⟨B0 - lo0, by omega, by omega⟩, ⟨B1 - lo1, by omega, by omega⟩⟩, rfl⟩
    rw [hlen]
    by_cases h : lo0 ≤ B0 ∧ B0 < lo0 + n ∧ lo1 ≤ B1 ∧ B1 < lo1 + n1
    · rw [if_pos (hmem.mpr h), if_pos h, if_pos ⟨h.1, by omega, h.2.2⟩]
    · rw [if_neg (fun h' => h (hmem.mp h'))]
      by_cases hz : ((lo0 : ℕ) : ℤ) - B0 + (n : ℤ) = 0 ∧ lo1 ≤ B1 ∧ B1 < lo1 + n1
      · rw [if_pos hz, if_pos ⟨by omega, by omega, hz.2⟩]
        have : B0 - lo0 = n := by omega
        rw [this]
        ring
      · rw [if_neg hz]
        rw [if_neg (by omega)]
        ring

end NearQuarticWires.Reconstruct
