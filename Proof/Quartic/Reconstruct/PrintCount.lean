import Proof.Quartic.Reconstruct.PrintLink3

/-!
# The context and the number of tables

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`contextWord_eq`: the context in the fields computed by the printing stage; `tablesPerGroup_eq`: the tables of one
group, `Σ_p p · Q_p`; `printList_length_eq`: the number `512 A₀ A₁ · (tables per group)` of printed tables.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord kindTag)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

theorem kindTag_bit (q : ChildRequest B1 B2) :
    (if kindTag q.call.kind = 1 then 1 else 0) = pairBit q := by
  classical
  unfold pairBit
  cases h : q.call.kind <;> simp [kindTag]

theorem groupSize_eq (pb p : ℕ) : groupSize pb p = p * resQ pb p := by
  unfold groupSize resQ; split <;> simp

theorem residueListOf_length (q : ChildRequest B1 B2) (p : ℕ) :
    (residueListOf q p).length = p * resQ (pairBit q) p := by
  rw [residueListOf_eq, List.length_flatMap]
  simp only [List.length_map, List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]

/-- **The tables of one group.** -/
theorem tablesPerGroup_eq (q : ChildRequest B1 B2) :
    tablesPerGroup q = ((q.selected.1.primes.sort (· ≤ ·)).map (groupSize (pairBit q))).sum := by
  unfold tablesPerGroup
  rw [List.length_flatMap]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [residueListOf_length, groupSize_eq]

/-- **The context of a child** in the fields of the printing stage. -/
theorem contextWord_eq (q : ChildRequest B1 B2) :
    contextWord q = ctxWordOf q.call.n q.selected.1.M1 q.selected.1.A q.selected.1.Lambda q.cellCall.J
      (if kindTag q.call.kind = 1 then 1 else 0) (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
      (2 * Algorithm.traceOrder * Builder.occurrences q.call 1) q.cellCall.ncol
      ((q.selected.1.primes.sort (· ≤ ·)).map (groupSize (pairBit q))).sum q.selected.1.factors
      (certifiedBits q.cellCall) := by
  classical
  rw [kindTag_bit, ← tablesPerGroup_eq]
  unfold contextWord ctxWordOf pairBit
  congr 6
  unfold bitWord
  split <;> simp_all

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (c : ℕ) (h : ∀ a ∈ l, (f a).length = c) :
    (l.flatMap f).length = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (by simp), ih (fun b hb => h b (by simp [hb])), List.length_cons]
    ring

/-- **The number of printed tables.** -/
theorem printList_length_eq (q : ChildRequest B1 B2) :
    (printList q).length = 512 * baseOf q ^ (q.cellCall.J + 1) * a1Of q * tablesPerGroup q := by
  have hg : ∀ (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ),
      ((primeList q.cellCall).attach.flatMap fun p => (residueListOf q p.1).map fun ρ =>
        printRequestOf q s σ δ p ρ).length = tablesPerGroup q := by
    intro s σ δ
    unfold tablesPerGroup
    rw [List.length_flatMap, List.length_flatMap]
    simp only [List.length_map]
    rw [show ((primeList q.cellCall).attach.map fun p => (residueListOf q p.1).length) =
      ((primeList q.cellCall).attach.map Subtype.val).map (fun p => (residueListOf q p).length) by
        rw [List.map_map]; rfl, List.attach_map_subtype_val]
  have hd : (digitList q).length = baseOf q ^ (q.cellCall.J + 1) * a1Of q := by
    rw [digitList_eq, length_flatMap_const _ _ (a1Of q) (fun x0 _ => by simp)]
    simp
  have hp : patternList.length = 256 := by rw [patternList_eq]; simp
  unfold printList
  rw [length_flatMap_const _ _ (256 * (baseOf q ^ (q.cellCall.J + 1) * a1Of q * tablesPerGroup q)) (fun s _ => by
    rw [length_flatMap_const _ _ (baseOf q ^ (q.cellCall.J + 1) * a1Of q * tablesPerGroup q) (fun σ _ => by
      rw [length_flatMap_const _ _ (tablesPerGroup q) (fun δ _ => hg s σ δ), hd]), hp])]
  simp only [List.length_cons, List.length_nil]
  ring

end NearQuarticWires.Reconstruct
