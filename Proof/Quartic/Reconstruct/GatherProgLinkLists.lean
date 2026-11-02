import Proof.Quartic.Reconstruct.GatherProgRun
import Proof.Quartic.Reconstruct.EmitStage

/-!
# The gathering program: list lemmas for the link to the words

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

Positional facts used to identify the numbers written by the gathering program with the gathered items: a
`flatMap` over the positions of a list (`range_flatMap_eq`), the positions of a `flatMap` of equal-length blocks
(`flatMap_getD_uniform`), and the certified counts of a table in the order of `certList` (`cnts_certNats`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct

theorem range_flatMap_eq {α β : Type} (L : List α) (g : ℕ → List β) (h : α → List β)
    (hgh : ∀ k (hk : k < L.length), g k = h L[k]) : (List.range L.length).flatMap g = L.flatMap h := by
  induction L generalizing g with
  | nil => rfl
  | cons a L ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.flatMap_cons]
    rw [hgh 0 (by simp)]
    congr 1
    exact ih (fun k => g (k + 1)) (fun k hk => by rw [hgh (k + 1) (by simp; omega)]; rfl)

theorem flatMap_getD_uniform {α : Type} (L : List α) (f : α → List ℕ) (n : ℕ)
    (hf : ∀ a ∈ L, (f a).length = n) (k i : ℕ) (hk : k < L.length) (hi : i < n) :
    (L.flatMap f).getD (n * k + i) 0 = (f L[k]).getD i 0 := by
  induction L generalizing k with
  | nil => simp at hk
  | cons a L ih =>
    have ha : (f a).length = n := hf a List.mem_cons_self
    rw [List.flatMap_cons]
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by omega)]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith)]
      have e : n * (k + 1) + i - (f a).length = n * k + i := by rw [ha]; ring_nf; omega
      rw [e]
      exact ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)) k (by simp at hk; omega)

/-- `0` or `1` for a bit. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

variable {B1 B2 : ℕ}

theorem certNats_eq (q : ChildRequest B1 B2) :
    certNats q = (List.finRange q.cellCall.ncol).map fun z => bitNat (decide (z ∈ q.cellCall.certifiedColumns)) := by
  classical
  unfold certNats certifiedBits bitNat
  rw [List.ofFn_eq_map, List.map_map]
  rfl

theorem certList_eq (q : ChildRequest B1 B2) :
    certList q = (List.finRange q.cellCall.ncol).filter fun z => decide (z ∈ q.cellCall.certifiedColumns) := by
  classical
  unfold certList
  rfl

theorem cnts_finRange {n : ℕ} (e : Fin n → ℤ) (c : Fin n → Bool) (L : List (Fin n)) :
    cnts (L.map e) (L.map fun z => bitNat (c z)) = (L.filter c).map fun z => (e z).toNat := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    unfold cnts at ih ⊢
    simp only [bitNat] at ih ⊢
    simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons, List.filter_cons]
    cases hc : c z <;> simp [hc, ih]

theorem ents_eq (q : ChildRequest B1 B2) (ents : List ℤ) (h : ents.length = q.cellCall.ncol) :
    ents = (List.finRange q.cellCall.ncol).map fun z => ents.getD z.val 0 := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [List.getElem?_eq_getElem h1]

/-- **The certified counts of a table** in the order of `certList`. -/
theorem cnts_certNats (q : ChildRequest B1 B2) (ents : List ℤ) (h : ents.length = q.cellCall.ncol) :
    cnts ents (certNats q) = (certList q).map fun z => (ents.getD z.val 0).toNat := by
  classical
  conv_lhs => rw [ents_eq q ents h, certNats_eq]
  rw [cnts_finRange, certList_eq]

theorem ncOf_certNats (q : ChildRequest B1 B2) : ncOf (certNats q) = (certList q).length := by
  classical
  rw [certNats_eq, certList_eq]
  unfold ncOf
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro z _
  unfold bitNat
  by_cases hz : z ∈ q.cellCall.certifiedColumns <;> simp [hz]

theorem certNats_le_one (q : ChildRequest B1 B2) : ∀ b ∈ certNats q, b ≤ 1 := certNats_le q

theorem sum_eq_ncOf (bits : List ℕ) (h : ∀ b ∈ bits, b ≤ 1) : bits.sum = ncOf bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    unfold ncOf at ih ⊢
    have hb := h b List.mem_cons_self
    rw [List.sum_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.filter_cons]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> simp <;> omega

end NearQuarticWires.Reconstruct.GatherProg
