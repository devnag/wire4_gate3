import Proof.Quartic.Cells.Printing

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Compiler
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: enumerate every walk's literal signed equation list in order. -/
def compiledTable {n V T : ℕ} {ZL ZR : Type} (B : ℕ)
    (atoms : Fin T → Fin V → NormalizedThresholdGate n)
    (coords : Fin T → Fin V → HalfCoords n ZL ZR) (F : Fin T → Formula V) :
    SignedOccurrenceList ZL ZR :=
  (List.ofFn fun w => compiledFormula B (atoms w) (coords w) (F w)).flatten

/-- `lem:print`, paper/paper.tex: the table is the actual integer sum over all walk formulas. -/
theorem compiledTable_value {n V T : ℕ} {ZL ZR : Type} (B : ℕ)
    (atoms : Fin T → Fin V → NormalizedThresholdGate n)
    (coords : Fin T → Fin V → HalfCoords n ZL ZR) (F : Fin T → Formula V)
    (hB : ∀ w i, GateBits B (atoms w i)) (zl : ZL) (zr : ZR) :
    (compiledTable B atoms coords F).value zl zr =
      ∑ w, (F w).eval (boolPoint fun i => (atoms w i).eval ((coords w i).point zl zr)) := by
  unfold compiledTable SignedOccurrenceList.value
  rw [List.map_flatten, List.sum_flatten, List.map_map]
  change ((List.ofFn fun w => compiledFormula B (atoms w) (coords w) (F w)).map
    (fun es => es.value zl zr)).sum = _
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro w _
  exact compiledFormula_value B (atoms w) (coords w) (F w) (hB w) zl zr

/-- `lem:print`, paper/paper.tex: the complete list has at most T Uocc^D equations. -/
theorem compiledTable_length {n V T : ℕ} {ZL ZR : Type} (hn : 0 < n) (B D Uocc : ℕ)
    (atoms : Fin T → Fin V → NormalizedThresholdGate n)
    (coords : Fin T → Fin V → HalfCoords n ZL ZR) (F : Fin T → Formula V)
    (hB : ∀ w i, GateBits B (atoms w i)) (hD : ∀ w, (F w).degree ≤ D)
    (hU : 1 + V * childCap n B ≤ Uocc) :
    (compiledTable B atoms coords F).length ≤ T * Uocc ^ D := by
  unfold compiledTable
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc ∑ w, (compiledFormula B (atoms w) (coords w) (F w)).length ≤
      ∑ _w : Fin T, Uocc ^ D := Finset.sum_le_sum fun w _ =>
        compiledFormula_length hn B D Uocc (atoms w) (coords w) (F w) (hB w) (hD w) hU
    _ = _ := by simp

/-- `imp:printer` and `lem:print`, paper/paper.tex: exact signed equation tables are
literally weighted-dominance tables on the separated center halves. This is the algebraic printer dock. -/
theorem compiledTable_weightedDominance {n V T R C : ℕ} {ZL ZR : Type} (B : ℕ)
    (atoms : Fin T → Fin V → NormalizedThresholdGate n)
    (coords : Fin T → Fin V → HalfCoords n ZL ZR) (F : Fin T → Formula V)
    (hB : ∀ w i, GateBits B (atoms w i)) (rowOf : Fin R → ZL) (colOf : Fin C → ZR)
    (r : Fin R) (c : Fin C) :
    NearCubicWires.SupplierPrinter.weightedDominance
      (cutLeft (compiledTable B atoms coords F) rowOf)
      (cutRight (compiledTable B atoms coords F) colOf)
      (cutWeight (compiledTable B atoms coords F)) r c =
    ∑ w, (F w).eval (boolPoint fun i => (atoms w i).eval ((coords w i).point (rowOf r) (colOf c))) := by
  rw [← value_eq_weightedDominance]
  exact compiledTable_value B atoms coords F hB _ _

end NearQuarticWires.Cells
