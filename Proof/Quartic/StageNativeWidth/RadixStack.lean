import Proof.Quartic.StageNativeWidth.StackBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeWidth

open NearCubicGates.Close.TabMachine NearCubicGates.Close.WordPrograms

theorem nat_mem_le_sum (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have h := ih hx
      simp only [List.sum_cons]
      omega

theorem entry_le_magL (ls : List (List ℤ)) (row : List ℤ) (hr : row ∈ ls)
    (z : ℤ) (hz : z ∈ row) : z.natAbs ≤ magL ls :=
  (nat_mem_le_sum (row.map Int.natAbs) z.natAbs (List.mem_map_of_mem hz)).trans
    (nat_mem_le_sum (ls.map fun row => (row.map Int.natAbs).sum) _ (List.mem_map_of_mem hr))

/-- `lem:print`, paper/paper.tex: the actual
radix magL+1 dominates every signed entry of the concrete Horner stack. -/
theorem stackL_radix_abs (s M : ℕ) (ls : List (List ℤ))
    (h : ∀ row ∈ ls, ∀ z ∈ row, z.natAbs ≤ M) :
    ∀ z ∈ stackL s ((M+1 : ℕ) : ℤ) ls, z.natAbs < (M+1)^ls.length := by
  have hzip : ∀ (xs ys : List ℤ) (B : ℕ),
      (∀ x ∈ xs, x.natAbs ≤ M) → (∀ y ∈ ys, y.natAbs < B) →
      ∀ z ∈ List.zipWith (fun a c => a + ((M+1 : ℕ) : ℤ) * c) xs ys,
        z.natAbs < (M+1)*B := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      intro ys B hx hy
      cases ys with
      | nil => simp
      | cons y ys =>
        intro z hz
        simp only [List.zipWith_cons_cons, List.mem_cons] at hz
        rcases hz with rfl | hz
        · have ha := hx x (by simp)
          have hc := hy y (by simp)
          have ht := Int.natAbs_add_le x (((M+1 : ℕ) : ℤ) * y)
          rw [Int.natAbs_mul, Int.natAbs_natCast] at ht
          have hm := Nat.mul_le_mul_left (M+1) (show y.natAbs+1 ≤ B by omega)
          nlinarith only [ha, ht, hm]
        · exact ih ys B (fun a ha => hx a (by simp [ha]))
            (fun a ha => hy a (by simp [ha])) z hz
  induction ls with
  | nil =>
    intro z hz
    have he : z = 0 := List.eq_of_mem_replicate hz
    simp [he]
  | cons row ls ih =>
    have ht := ih (fun a ha => h a (by simp [ha]))
    intro z hz
    have hh := hzip row (stackL s ((M+1 : ℕ) : ℤ) ls) ((M+1)^ls.length)
      (h row (by simp)) ht z hz
    simpa only [List.length_cons, pow_succ, Nat.mul_comm] using hh

/-- `lem:print`, paper/paper.tex: the exact
StackRequest radix-power guard bounds every literal packed field,
without replacing its actual base by a different Horner envelope. -/
theorem cutL_abs_of_stack_fit (W s : ℕ) (ls : List (List ℤ)) (c : ℤ)
    (hst : (magL ls+1)^(ls.length+1) < 2^W) (hc : SInt.encS c < 2^(W+1)) :
    ∀ z ∈ cutL s c ls, z.natAbs < 2^W := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · have hh := stackL_radix_abs s (magL ls) ls (entry_le_magL ls) z hz
    have hm : (magL ls+1)^ls.length ≤ (magL ls+1)^(ls.length+1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact hh.trans (hm.trans_lt hst)
  · have he := List.mem_singleton.mp hz
    subst z
    have hmag : 2*c.natAbs ≤ SInt.encS c := by unfold SInt.encS; split_ifs <;> omega
    rw [pow_succ] at hc
    omega

end NearQuarticWires.StageNativeWidth
