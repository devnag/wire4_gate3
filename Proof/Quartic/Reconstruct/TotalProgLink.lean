import Proof.Quartic.Reconstruct.TotalProgRun
import Proof.Quartic.Reconstruct.GatherProgBounds

/-!
# The sum of the answers: the link to the words

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

The word after `solved` is the numbers of the answered systems of `systemList` (`itD`, `solvedWord_nats`), and the
difference of the two sums of the program is the child objective `Ψ̃(π)` (`childObjective_eq_sums`, from
`childObjective_eq_systemList`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.TotalProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord ratWord)
open NearCubicGates.Close.Interfaces.Formats (SolveMachine solveWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct NearQuarticWires.Reconstruct.GatherProg

variable {B1 B2 : ℕ}

/-- The sign of an integer as a number. -/
def sgnN (z : ℤ) : ℕ := if z < 0 then 1 else 0

/-- The numbers of a rational value. -/
def ratN (f : ℚ) : ℕ × ℕ × ℕ := (sgnN f.num, f.num.natAbs, f.den)

/-- **The answered system** `x` as the program reads it. -/
noncomputable def itD (q : ChildRequest B1 B2) (S : SolveMachine) (x : SystemIndex q) : ItD :=
  ⟨sgnN (systemCoef q x), (systemCoef q x).natAbs, (systemAt q x).pts.idxOf [0, 0],
    (S.solve (systemAt q x)).map fun F => F.map ratN⟩

/-- The answered systems of a child. -/
noncomputable def itsQ (q : ChildRequest B1 B2) (S : SolveMachine) : List ItD := (systemList q).map (itD q S)

theorem intWord_nats (z : ℤ) : NearCubicGates.Close.Interfaces.intWord z = [sgnN z, z.natAbs].flatMap natWord := by
  simp [NearCubicGates.Close.Interfaces.intWord, sgnN]

theorem itN_word (q : ChildRequest B1 B2) (S : SolveMachine) (x : SystemIndex q) :
    (itN (itD q S x)).flatMap natWord = systemTag q x ++ solveWord (S.solve (systemAt q x)) := by
  unfold itN itD systemTag
  rw [List.flatMap_append, intWord_nats]
  congr 1
  · simp
  · cases S.solve (systemAt q x) with
    | none => rfl
    | some F =>
      simp only [Option.map_some, ansN, solveWord, listWord, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_map, List.cons_append, List.nil_append, List.flatMap_append, List.flatMap_map, List.append_assoc]
      congr 2
      rw [List.flatMap_assoc]
      refine List.flatMap_congr fun f _ => ?_
      simp [entN, ratN, ratWord, NearCubicGates.Close.Interfaces.intWord, sgnN]

/-- **The input of the sum.** -/
theorem solvedWord_nats (q : ChildRequest B1 B2) (S : SolveMachine) :
    solvedWord q S = (q.call.n :: (itsQ q S).length :: (itsQ q S).flatMap itN).flatMap natWord := by
  unfold solvedWord listWord itsQ
  simp only [List.flatMap_cons, List.length_map, List.flatMap_map, List.flatMap_assoc]
  congr 2
  exact List.flatMap_congr fun x _ => (itN_word q S x).symm

theorem signed_prod (a b : ℤ) : a * b =
    if sgnN a = sgnN b then ((a.natAbs * b.natAbs : ℕ) : ℤ) else -((a.natAbs * b.natAbs : ℕ) : ℤ) := by
  unfold sgnN
  push_cast
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · rw [if_pos ha, if_pos hb, if_pos rfl, abs_of_neg ha, abs_of_neg hb]; ring
  · rw [if_pos ha, if_neg hb, if_neg (by norm_num), abs_of_neg ha, abs_of_nonneg (not_lt.mp hb)]; ring
  · rw [if_neg ha, if_pos hb, if_neg (by norm_num), abs_of_nonneg (not_lt.mp ha), abs_of_neg hb]; ring
  · rw [if_neg ha, if_neg hb, if_pos rfl, abs_of_nonneg (not_lt.mp ha), abs_of_nonneg (not_lt.mp hb)]

theorem term_eq (q : ChildRequest B1 B2) (S : SolveMachine) (x : SystemIndex q) :
    systemCoef q x * (solvedRead S (systemAt q x)).num = (posOf (itD q S x) : ℤ) - negOf (itD q S x) := by
  have hv : valOf (itD q S x) = (sgnN (solvedRead S (systemAt q x)).num,
      (solvedRead S (systemAt q x)).num.natAbs) := by
    unfold valOf itD solvedRead
    cases h : S.solve (systemAt q x) with
    | none => simp [sgnN]
    | some F =>
      simp only [Option.map_some, List.length_map]
      by_cases hi : (systemAt q x).pts.idxOf [0, 0] < F.length
      · rw [if_pos hi, List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
        simp [ratN]
      · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
        simp [sgnN]
  rw [signed_prod, posOf, negOf, prodOf, hv]
  simp only [itD]
  split_ifs <;> push_cast <;> ring

/-- **The child objective is the difference of the two sums of the program.** -/
theorem childObjective_eq_sums (q : ChildRequest B1 B2) (S : SolveMachine) :
    childObjective q = (((itsQ q S).map posOf).sum : ℤ) - (((itsQ q S).map negOf).sum : ℤ) := by
  rw [childObjective_eq_systemList S q, itsQ]
  simp only [List.map_map]
  rw [List.map_congr_left (fun x _ => term_eq q S x)]
  induction systemList q with
  | nil => simp
  | cons x L ih => simp only [List.map_cons, List.sum_cons, Function.comp, ih]; push_cast; ring

end NearQuarticWires.Reconstruct.TotalProg
