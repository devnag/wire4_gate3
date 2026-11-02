import Proof.Quartic.Reconstruct.ForLoop

/-!
# Enumerating vectors by a counter

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the printed tables run over the patterns `σ`,
the digit vectors `δ` and the residue vectors `ρ_Y`).

The printing stage enumerates `vecList L k` (`Lists.vecList`, the first coordinate outermost) by a counter
`i < |L|^k`: coordinate `j` of the `i`-th vector is entry `(i / |L|^(k-1-j)) % |L|` of `L` (`vecList_eq_range`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

/-- `range (n * m)` as `n` consecutive blocks of `m`. -/
theorem range_mul_flatMap (n m : ℕ) :
    List.range (n * m) = (List.range n).flatMap fun a => (List.range m).map fun b => a * m + b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The `i`-th vector of `vecList L k`. -/
def vecAt {α : Type} (L : List α) (d : α) (k i : ℕ) : Fin k → α :=
  fun j => L.getD ((i / L.length ^ (k - 1 - j)) % L.length) d

theorem list_eq_range_map {α : Type} (L : List α) (d : α) : L = (List.range L.length).map fun i => L.getD i d := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem h1]

theorem vecAt_succ {α : Type} (L : List α) (d : α) (k a b : ℕ) (ha : a < L.length) (hb : b < L.length ^ k) :
    vecAt L d (k + 1) (a * L.length ^ k + b) = Fin.cons (L.getD a d) (vecAt L d k b) := by
  have hL : 0 < L.length := by omega
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [vecAt, Fin.cons_zero, Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
    congr 1
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (pow_pos hL _), Nat.div_eq_of_lt hb, Nat.zero_add,
      Nat.mod_eq_of_lt ha]
  · simp only [vecAt, Fin.cons_succ, Fin.val_succ]
    congr 1
    have hk : k + 1 - 1 - (j.val + 1) = k - 1 - j.val := by omega
    rw [hk]
    have hj : j.val < k := j.isLt
    have hpow : L.length ^ k = L.length ^ (k - 1 - j.val) * L.length ^ (j.val + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, Nat.mul_comm (L.length ^ (k - 1 - j.val)), ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_right _ _ (pow_pos hL _), Nat.add_comm, pow_succ, ← Nat.mul_assoc,
      show a * L.length ^ j.val * L.length = L.length * (a * L.length ^ j.val) by ring, Nat.mul_add_mod]

/-- **`vecList` by a counter.** -/
theorem vecList_eq_range {α : Type} (L : List α) (d : α) :
    ∀ k, vecList L k = (List.range (L.length ^ k)).map (vecAt L d k)
  | 0 => by
    simp only [vecList, pow_zero, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    funext j; exact j.elim0
  | k + 1 => by
    have hL := list_eq_range_map L d
    rw [vecList, vecList_eq_range L d k, pow_succ, Nat.mul_comm, range_mul_flatMap, List.map_flatMap]
    rw [show L ×ˢ (List.range (L.length ^ k)).map (vecAt L d k) =
      L.flatMap (fun a => ((List.range (L.length ^ k)).map (vecAt L d k)).map (Prod.mk a)) from rfl, List.map_flatMap]
    have key : ∀ F : α → List (Fin (k + 1) → α),
        L.flatMap F = ((List.range L.length).map fun i => L.getD i d).flatMap F := fun F => by rw [← hL]
    rw [key, List.flatMap_map]
    refine List.flatMap_congr fun a ha => ?_
    rw [List.map_map, List.map_map, List.map_map]
    refine List.map_congr_left fun b hb => ?_
    simp only [Function.comp, List.mem_range] at ha hb ⊢
    rw [vecAt_succ L d k a b ha hb]

end NearQuarticWires.Reconstruct
