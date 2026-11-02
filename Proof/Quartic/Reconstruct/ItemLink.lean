import Proof.Quartic.Reconstruct.ItemFull
import Proof.Quartic.Reconstruct.SystemLink

/-!
# The data of one gathered item from the child

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `lem:certify`(d).

For a listed system `x = (s, σ, δ, z)` with the context of the child (`M_1`, `A`, `Λ`, `2mG_j`, the rates) the box
computed by `itemAxesS` from the flattened digit vector is the box of `δ` (`axisTriple_zero`, `axisTriple_one`), and
the word written by `itemS` is the framed tag and the framed word of the system (`itemWord_eq`). The rest of the
file collects the facts about the child used by the run: `A, Λ ≥ 1`, the rates, the digits and the rows.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The flattened digit vector of an item. -/
theorem posDig_zero (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (i : ℕ)
    (hi : i ≤ q.cellCall.J) :
    posDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) 0 i = digitPart q δ 0 true i ∧
      negDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) 0 i = digitPart q δ 0 false i := by
  unfold posDig negDig
  rw [Nat.zero_add, digits_getD_zero δ i hi, digitPart_eq q δ 0 true i hi, digitPart_eq q δ 0 false i hi]
  exact ⟨rfl, rfl⟩

theorem posDig_one (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (i : ℕ)
    (hi : i ≤ q.cellCall.J) :
    posDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) (q.cellCall.J + 1) i = digitPart q δ 1 true i ∧
      negDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) (q.cellCall.J + 1) i = digitPart q δ 1 false i := by
  unfold posDig negDig
  rw [digits_getD_one δ i hi, digitPart_eq q δ 1 true i hi, digitPart_eq q δ 1 false i hi]
  exact ⟨rfl, rfl⟩

theorem zero_mem_circuitSet (c : NearCubicGates.Close.Interfaces.Call) : (0 : Fin 2) ∈ Builder.circuitSet c := by
  unfold Builder.circuitSet; split <;> simp

theorem one_mem_circuitSet (c : NearCubicGates.Close.Interfaces.Call) : (1 : Fin 2) ∈ Builder.circuitSet c ↔ c.kind = .pair := by
  unfold Builder.circuitSet
  by_cases h : c.kind = .pair
  · simp [h]
  · simp [h]

/-- **The first coordinate interval of an item.** -/
theorem axisTriple_zero (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :
    axisTriple q.selected.1.M1 q.selected.1.A q.selected.1.Lambda
        (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)
        (hornerN (fun i => q.selected.1.factors.getD i 0) (posDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) 0)
          q.cellCall.J)
        (hornerN (fun i => q.selected.1.factors.getD i 0) (negDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) 0)
          q.cellCall.J) = axisData q δ 0 := by
  classical
  have h1 := hornerN_congr (fun i => q.selected.1.factors.getD i 0) (fun i => q.selected.1.factors.getD i 0)
    (posDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) 0) (digitPart q δ 0 true) q.cellCall.J (fun _ _ => rfl)
    (fun i hi => (posDig_zero q δ i hi).1)
  have h2 := hornerN_congr (fun i => q.selected.1.factors.getD i 0) (fun i => q.selected.1.factors.getD i 0)
    (negDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) 0) (digitPart q δ 0 false) q.cellCall.J (fun _ _ => rfl)
    (fun i hi => (posDig_zero q δ i hi).2)
  rw [h1, h2]
  unfold axisData
  rw [if_pos (zero_mem_circuitSet q.call)]
  rfl

/-- **The second coordinate interval of an item.** -/
theorem axisTriple_one (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :
    (if decide (q.call.kind = .pair) then axisTriple q.selected.1.M1 q.selected.1.A q.selected.1.Lambda
        (2 * Algorithm.traceOrder * Builder.occurrences q.call 1)
        (hornerN (fun i => q.selected.1.factors.getD i 0)
          (posDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) (q.cellCall.J + 1)) q.cellCall.J)
        (hornerN (fun i => q.selected.1.factors.getD i 0)
          (negDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) (q.cellCall.J + 1)) q.cellCall.J) else (0, 1, 0)) =
      axisData q δ 1 := by
  classical
  by_cases hp : q.call.kind = .pair
  · have h1 := hornerN_congr (fun i => q.selected.1.factors.getD i 0) (fun i => q.selected.1.factors.getD i 0)
      (posDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) (q.cellCall.J + 1)) (digitPart q δ 1 true) q.cellCall.J
      (fun _ _ => rfl) (fun i hi => (posDig_one q δ i hi).1)
    have h2 := hornerN_congr (fun i => q.selected.1.factors.getD i 0) (fun i => q.selected.1.factors.getD i 0)
      (negDig (List.ofFn (δ 0) ++ List.ofFn (δ 1)) (q.cellCall.J + 1)) (digitPart q δ 1 false) q.cellCall.J
      (fun _ _ => rfl) (fun i hi => (posDig_one q δ i hi).2)
    rw [if_pos (by simpa using hp), h1, h2]
    unfold axisData
    rw [if_pos ((one_mem_circuitSet q.call).mpr hp)]
    rfl
  · rw [if_neg (by simpa using hp)]
    unfold axisData
    rw [if_neg (fun h => hp ((one_mem_circuitSet q.call).mp h))]

/-- **The word of one item is the framed tag and the framed word of its system.** -/
theorem itemWord_eq (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) :
    itemWord x.1 (axisData q x.2.2.1 0).1 (axisData q x.2.2.1 0).2.1 (axisData q x.2.2.1 0).2.2
        (axisData q x.2.2.1 1).1 (axisData q x.2.2.1 1).2.1 (axisData q x.2.2.1 1).2.2 (systemAt q x).rows =
      RepairOrdinary.frame (systemTag q x) ++
        RepairOrdinary.frame (NearCubicGates.Close.Interfaces.Formats.sysWord (systemAt q x)) := by
  rw [systemTag_eq q x hx, sysWord_systemAt]
  rfl

/-! ## Facts about the child -/

theorem one_le_A (q : ChildRequest B1 B2) : 1 ≤ q.selected.1.A := by
  have H := reconstructionHypotheses_of_dispatch q.dispatched q.witness
  have hpos : 0 < q.cellCall.ncol := Nat.two_pow_pos _
  have h := H.A_pos ⟨0, hpos⟩
  change (0 : ℤ) < (q.selected.1.A : ℤ) at h
  exact_mod_cast h

theorem one_le_Lambda (q : ChildRequest B1 B2) : 1 ≤ q.selected.1.Lambda := by
  rw [(rules q).Lambda_eq]
  omega

theorem factors_length (q : ChildRequest B1 B2) : q.selected.1.factors.length = q.cellCall.J := by
  rw [(rules q).factors_eq]
  unfold NearCubicGates.Close.Counter.chainFactors
  simp only [List.length_map, List.length_range]
  rfl

theorem factors_getD_le (q : ChildRequest B1 B2) (i : ℕ) : q.selected.1.factors.getD i 0 ≤ q.call.n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : q.selected.1.factors[i]? with
  | none => simp
  | some v =>
    exact Cells.ParameterRules.factor_member_preparation_bound (rules q) v (List.mem_of_getElem? hi)

/-- The digits of a listed system lie in `(-h_E, h_E)`. -/
theorem digits_natAbs_le (q : ChildRequest B1 B2) (x : SystemIndex q) (hx : x ∈ systemList q) :
    ∀ z ∈ List.ofFn (x.2.2.1 0) ++ List.ofFn (x.2.2.1 1), z.natAbs ≤ q.selected.1.hE := by
  classical
  have hδ := (mem_systemList hx).2.1
  unfold digitSet at hδ
  rw [Fintype.mem_piFinset] at hδ
  have key : ∀ j i, (x.2.2.1 j i).natAbs ≤ q.selected.1.hE := by
    intro j i
    have h := hδ j
    split at h
    · rw [Fintype.mem_piFinset] at h
      have := Finset.mem_Ioo.mp (h i)
      omega
    · rw [Finset.mem_singleton] at h
      rw [h]
      simp
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact key 0 i
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact key 1 i

theorem digits_length (q : ChildRequest B1 B2) (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) :
    (List.ofFn (δ 0) ++ List.ofFn (δ 1)).length = 2 * (q.cellCall.J + 1) := by
  simp; ring

theorem systemAt_rows_two (q : ChildRequest B1 B2) (x : SystemIndex q) :
    ∀ row ∈ (systemAt q x).rows, row.2.1.length = 2 := by
  intro row hrow
  obtain ⟨p, -, ρ, -, rfl⟩ := (mem_systemRows _ _ _ _ _ row).mp hrow
  rfl

end NearQuarticWires.Reconstruct
