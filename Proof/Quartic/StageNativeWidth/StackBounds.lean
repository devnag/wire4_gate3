import Proof.Quartic.StageNativeWidth.SourceBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicWires
open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: every literal
Horner pair has its sum-of-magnitudes bound, including signed entries. -/
theorem zipWith_abs (b P Q : ℕ) (xs ys : List ℤ)
    (hx : ∀ x ∈ xs, x.natAbs ≤ P) (hy : ∀ y ∈ ys, y.natAbs ≤ Q) :
    ∀ z ∈ List.zipWith (fun a c => a + (b : ℤ) * c) xs ys, z.natAbs ≤ P + b * Q := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      intro z hz
      simp only [List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · have h := Int.natAbs_add_le x ((b : ℤ) * y)
        rw [Int.natAbs_mul, Int.natAbs_natCast] at h
        exact h.trans (Nat.add_le_add (hx x (by simp))
          (Nat.mul_le_mul_left _ (hy y (by simp))))
      · exact ih ys (fun a ha => hx a (by simp [ha])) (fun a ha => hy a (by simp [ha])) z hz

/-- `lem:print`, paper/paper.tex: the concrete
list stackL obeys the actual Horner bound, with no coordinate-layout
or identity-generator hypothesis and with the empty tuple retained. -/
theorem stackL_abs (s b P : ℕ) (ls : List (List ℤ))
    (h : ∀ row ∈ ls, ∀ z ∈ row, z.natAbs ≤ P) :
    ∀ z ∈ stackL s (b : ℤ) ls, z.natAbs ≤ P * (b+1)^ls.length := by
  induction ls with
  | nil =>
    intro z hz
    have he : z = 0 := List.eq_of_mem_replicate hz
    simp [he]
  | cons row ls ih =>
    have ht := ih (fun a ha => h a (by simp [ha]))
    have hp : P ≤ P * (b+1)^ls.length :=
      Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
    intro z hz
    have hh := zipWith_abs b P (P * (b+1)^ls.length) row (stackL s (b : ℤ) ls)
      (h row (by simp)) ht z hz
    change z.natAbs ≤ P * (b+1)^(ls.length+1)
    calc
      _ ≤ P + b * (P * (b+1)^ls.length) := hh
      _ ≤ P * (b+1)^ls.length + b * (P * (b+1)^ls.length) := Nat.add_le_add_right hp _
      _ = _ := by ring

/-- `lem:print`, paper/paper.tex: source signed
field bounds control the literal sum magL over the actual chosen rows. -/
theorem magL_le (L s D : ℕ) (ls : List (List ℤ)) (hl : ls.length ≤ D)
    (h : ∀ row ∈ ls, row.length = s+1 ∧ ∀ z ∈ row, SInt.encS z < 2^L) :
    magL ls ≤ D * ((s+1) * 2^L) := by
  have hm : ∀ row ∈ ls, (row.map Int.natAbs).sum ≤ (s+1) * 2^L := by
    intro row hr
    have hh := List.sum_le_card_nsmul (row.map Int.natAbs) (2^L) (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
      exact (natAbs_le_encS z).trans ((h row hr).2 z hz).le)
    simpa only [List.length_map, (h row hr).1, smul_eq_mul] using hh
  have hh := List.sum_le_card_nsmul (ls.map fun row => (row.map Int.natAbs).sum)
    ((s+1) * 2^L) (by
      intro v hv
      obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hv
      exact hm row hr)
  change magL ls ≤ _
  have hb : magL ls ≤ ls.length * ((s+1) * 2^L) := by
    simpa only [magL, List.length_map, smul_eq_mul] using hh
  exact hb.trans (Nat.mul_le_mul_right _ hl)

end NearQuarticWires.StageNativeWidth
