import Proof.Quartic.Reconstruct.PrintSetup

/-!
# The printed tables in the order of the counters

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The lists of `printList` by counters: the patterns (`patternList_eq`), the digit vectors of a circuit
(`digitAxisList_eq`) and the coordinates of a vector of the counter (`ofFn_vecAt`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

theorem ofFn_vecAt {α : Type} (L : List α) (d : α) (k i : ℕ) :
    List.ofFn (vecAt L d k i) = (List.range k).map fun j => L.getD ((i / L.length ^ (k - 1 - j)) % L.length) d := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp [vecAt]

theorem patternList_eq : patternList = (List.range 256).map (vecAt [false, true] false 8) := by
  unfold patternList
  rw [vecList_eq_range [false, true] false]
  rfl

theorem bitWord_getD (x : ℕ) : bitWord ([false, true].getD (x % 2) false) = natWord (x % 2) := by
  have : x % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases h : x % 2 <;> rfl

/-- The digits of a circuit. -/
noncomputable def digitL (q : ChildRequest B1 B2) : List ℤ :=
  intervalList (-(q.selected.1.hE : ℤ) + 1) ((q.selected.1.hE : ℤ) - 1)

theorem digitL_length (q : ChildRequest B1 B2) : (digitL q).length = 2 * q.selected.1.hE - 1 := by
  unfold digitL; rw [intervalList_length]; omega

theorem digitL_getD (q : ChildRequest B1 B2) (t : ℕ) (ht : t < 2 * q.selected.1.hE - 1) :
    (digitL q).getD t 0 = ((t : ℕ) : ℤ) - ((q.selected.1.hE - 1 : ℕ) : ℤ) := by
  unfold digitL intervalList
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp
  omega

theorem digitAxisList_zero (q : ChildRequest B1 B2) :
    digitAxisList q 0 = (List.range ((2 * q.selected.1.hE - 1) ^ (q.cellCall.J + 1))).map
      (vecAt (digitL q) 0 (q.cellCall.J + 1)) := by
  classical
  unfold digitAxisList
  rw [if_pos (zero_mem_circuitSet q.call), vecList_eq_range _ 0, ← digitL_length]
  rfl

theorem digitAxisList_one (q : ChildRequest B1 B2) :
    digitAxisList q 1 = if q.call.kind = .pair then (List.range ((2 * q.selected.1.hE - 1) ^ (q.cellCall.J + 1))).map
      (vecAt (digitL q) 0 (q.cellCall.J + 1)) else [0] := by
  classical
  unfold digitAxisList
  by_cases h : q.call.kind = .pair
  · rw [if_pos ((one_mem_circuitSet q.call).mpr h), if_pos h, vecList_eq_range _ 0, ← digitL_length]
    rfl
  · rw [if_neg (fun h' => h ((one_mem_circuitSet q.call).mp h')), if_neg h]

end NearQuarticWires.Reconstruct
