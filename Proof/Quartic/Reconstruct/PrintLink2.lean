import Proof.Quartic.Reconstruct.PrintLink

/-!
# The index of a printed table from the counters

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `Greedy.printIndexWord`.

`index_marks`: for the request of the counters `(iS, is, x₀, x₁, p, y₀, y₁)`, the index word at depth `2` is the word
`printIdxW …` written by `printIdxS`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- `1` when the call has two circuits. -/
noncomputable def pairBit (q : ChildRequest B1 B2) : ℕ := by
  classical
  exact if q.call.kind = .pair then 1 else 0

/-- The digit base of a child. -/
noncomputable def baseOf (q : ChildRequest B1 B2) : ℕ := 2 * q.selected.1.hE - 1

/-- The number of digit vectors of the second circuit. -/
noncomputable def a1Of (q : ChildRequest B1 B2) : ℕ := if pairBit q = 1 then baseOf q ^ (q.cellCall.J + 1) else 1

/-- The second digit vector of the counter `x₁`. -/
noncomputable def dig1 (q : ChildRequest B1 B2) (x : ℕ) : Fin (q.cellCall.J + 1) → ℤ :=
  if pairBit q = 1 then vecAt (digitL q) 0 (q.cellCall.J + 1) x else 0

theorem listWord_marks_flatMap {α : Type} (f : α → List Bool) (l : List α) :
    marksD 2 (listWord f l) = marksD 2 (natWord l.length) ++ l.flatMap fun x => marksD 2 (f x) := by
  unfold listWord; rw [marksD_append, marksD_flatMap]

/-- The digits of the first circuit. -/
theorem digits_marks (q : ChildRequest B1 B2) (x : ℕ) (hE : 1 ≤ q.selected.1.hE) :
    (List.ofFn (vecAt (digitL q) 0 (q.cellCall.J + 1) x)).flatMap
        (fun z => marksD 2 (NearCubicGates.Close.Interfaces.intWord z)) =
      (List.range (q.cellCall.J + 1)).flatMap fun j => marksD 2 (NearCubicGates.Close.Interfaces.intWord
        ((((x / baseOf q ^ (q.cellCall.J + 1 - 1 - j)) % baseOf q : ℕ) : ℤ) - ((q.selected.1.hE - 1 : ℕ) : ℤ))) := by
  rw [ofFn_vecAt, List.flatMap_map, digitL_length]
  refine List.flatMap_congr fun j _ => ?_
  have hb : 0 < baseOf q := by unfold baseOf; omega
  rw [digitL_getD q _ (Nat.mod_lt _ (by unfold baseOf at hb; omega))]
  rfl

theorem dig1_marks (q : ChildRequest B1 B2) (x : ℕ) (hE : 1 ≤ q.selected.1.hE) (hx : pairBit q ≠ 1 → x = 0) :
    (List.ofFn (dig1 q x)).flatMap (fun z => marksD 2 (NearCubicGates.Close.Interfaces.intWord z)) =
      (List.range (q.cellCall.J + 1)).flatMap fun j => marksD 2 (NearCubicGates.Close.Interfaces.intWord
        ((((x / baseOf q ^ (q.cellCall.J + 1 - 1 - j)) % baseOf q : ℕ) : ℤ) -
          (((if pairBit q = 1 then q.selected.1.hE - 1 else 0) : ℕ) : ℤ))) := by
  by_cases hp : pairBit q = 1
  · unfold dig1; rw [if_pos hp, digits_marks q x hE]; simp only [if_pos hp]
  · have hx0 := hx hp
    subst hx0
    unfold dig1
    rw [if_neg hp]
    simp only [if_neg hp, Nat.zero_div, Nat.zero_mod, Nat.cast_zero, sub_zero]
    rw [show (List.ofFn (0 : Fin (q.cellCall.J + 1) → ℤ)) = (List.range (q.cellCall.J + 1)).map (fun _ => (0 : ℤ)) by
      apply List.ext_getElem (by simp); intro j h1 h2; simp; cases j <;> simp, List.flatMap_map]

/-- **The index word of the counters at depth `2`.** -/
theorem index_marks (q : ChildRequest B1 B2) (iS is x0 x1 p y0 y1 : ℕ) (hE : 1 ≤ q.selected.1.hE)
    (hx1 : pairBit q ≠ 1 → x1 = 0) :
    marksD 2 (bitWord (decide (iS = 0)) ++ listWord bitWord (List.ofFn (vecAt [false, true] false 8 is)) ++ natWord p ++
        listWord NearCubicGates.Close.Interfaces.intWord
          (List.ofFn (vecAt (digitL q) 0 (q.cellCall.J + 1) x0) ++ List.ofFn (dig1 q x1)) ++
        listWord NearCubicGates.Close.Interfaces.intWord [(y0 : ℤ), (y1 : ℤ)]) =
      printIdxW (if iS = 0 then 1 else 0) is p (2 * (q.cellCall.J + 1)) (baseOf q) (q.cellCall.J + 1) x0 x1
        (q.selected.1.hE - 1) (if pairBit q = 1 then q.selected.1.hE - 1 else 0) y0 y1 := by
  have hsb : bitWord (decide (iS = 0)) = natWord (if iS = 0 then 1 else 0) := by
    by_cases h : iS = 0 <;> simp [h, bitWord]
  have h8 : (List.ofFn (vecAt [false, true] false 8 is)).length = 8 := by simp
  have hl : (List.ofFn (vecAt (digitL q) 0 (q.cellCall.J + 1) x0) ++ List.ofFn (dig1 q x1)).length =
      2 * (q.cellCall.J + 1) := by simp; ring
  rw [marksD_append, marksD_append, marksD_append, marksD_append, hsb, listWord_marks_flatMap,
    listWord_marks_flatMap, listWord_marks_flatMap, h8, hl, List.flatMap_append, digits_marks q x0 hE,
    dig1_marks q x1 hE hx1, ofFn_vecAt, List.flatMap_map]
  unfold printIdxW
  have hb : (fun a => marksD 2 (bitWord ([false, true].getD (is / 2 ^ (8 - 1 - a) % 2) false))) =
      (fun j => marksD 2 (natWord ((is / 2 ^ (8 - 1 - j)) % 2))) := by funext j; rw [bitWord_getD]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.cast_zero, sub_zero, List.append_assoc]
  rw [hb]

end NearQuarticWires.Reconstruct
