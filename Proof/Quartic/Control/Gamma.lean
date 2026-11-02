import Proof.Quartic.Control.Coeff
import Proof.Quartic.Greedy.Child

/-!
# The coefficient requests of a child evaluation

Paper: `cor:conditional`, paper/paper.tex, and Step 3: the coefficient of the walk of
index `i` (in the order of `Greedy.walkList`) is requested by `Greedy.gammaRequest`. Its word is the fixed part
`natWord ℓ ++ natWord kh ++ natWord Q ++ natWord |π| ++ natWord code` followed by `natWord 8` and the base-`N` digits
of `i` (`gammaRequestWord_walk`), which is what `Control.writeRequest` writes from the walk index.
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.RepairRepresentation
open NearQuarticWires.Greedy

variable {B1 B2 : ℕ}

/-- The fixed part of the coefficient requests of a child evaluation. -/
noncomputable def requestHead (q : ChildRequest B1 B2) : List Bool :=
  natWord q.cellCall.seed.ell ++ natWord q.cellCall.seed.kh ++ natWord q.cellCall.seed.Q ++
    natWord q.seedPrefix.length ++ natWord (Algorithm.CellCall.prefixValue q.seedPrefix)

theorem walkList_getElem_val (N i : ℕ) (hi : i < (walkList N).length) (j : Fin (2 * Algorithm.traceOrder)) :
    ((walkList N)[i] j).val = i / N ^ (j : ℕ) % N := by
  simp only [walkList, List.getElem_ofFn]
  rfl

/-- **The request of the walk of index `i`.** -/
theorem gammaRequestWord_walk (q : ChildRequest B1 B2) (i : ℕ) (hi : i < (walkList q.cellCall.seed.N).length) :
    Machine.gammaRequestWord (gammaRequest q ((walkList q.cellCall.seed.N)[i])) =
      requestHead q ++ natWord 8 ++ (walkDigits q.cellCall.seed.kh 8 i).flatMap natWord := by
  unfold Machine.gammaRequestWord gammaRequest requestHead
  simp only [NearCubicGates.Close.Interfaces.listWord, List.length_ofFn]
  rw [walkDigits_eq]
  have hslots : (List.ofFn fun slot : Fin (2 * 4) => ((walkList q.cellCall.seed.N)[i] slot).val) =
      List.ofFn fun j : Fin 8 => i / (2 ^ q.cellCall.seed.kh) ^ (j : ℕ) % 2 ^ q.cellCall.seed.kh := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_ofFn]
    exact walkList_getElem_val _ i hi ⟨n, by simp at h1; simp [Algorithm.traceOrder]; omega⟩
  simp only [List.append_assoc]
  rw [hslots]


/-- The coefficient of the walk of index `i` (`0` beyond the last walk). -/
noncomputable def walkCoefficient (q : ChildRequest B1 B2) (i : ℕ) : ℤ :=
  if h : i < (walkList q.cellCall.seed.N).length then
    Machine.gammaTarget (gammaRequest q ((walkList q.cellCall.seed.N)[i])) else 0

/-- **The table of all the walks** is the marked coefficient table of the child (`Greedy.gammaTable`). -/
theorem tableMarks_gammaTable (q : ChildRequest B1 B2) :
    tableMarks (walkCoefficient q) (walkList q.cellCall.seed.N).length =
      NearCubicWires.RepairOrdinary.Streaming.marks
        ((gammaTable q).flatMap NearCubicGates.Close.Interfaces.intWord) := by
  have hmap : (List.range (walkList q.cellCall.seed.N).length).map (walkCoefficient q) = gammaTable q := by
    apply List.ext_getElem (by simp [gammaTable])
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, walkCoefficient, gammaTable]
    rw [dif_pos (by simpa using h1)]
    rfl
  unfold tableMarks
  rw [← hmap, List.flatMap_map]
  induction (List.range (walkList q.cellCall.seed.N).length) with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, NearCubicWires.RepairOrdinary.Streaming.marks_append, ih]

end NearQuarticWires.Control
