import Proof.Quartic.StagePrint.BuilderMomentSums
import Proof.Quartic.Cells.PrintingTable

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open scoped BigOperators
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Compiler
open NearQuarticWires NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator

/-- `sec:walks` and `lem:print`(b), paper/paper.tex: the canonical lowest-coordinate-first enumeration of all concrete closed walks. -/
def indexedWalk (N : ℕ) (i : Fin (N^8)) : Cycle.Walk N 4 :=
  finFunctionFinEquiv.symm i

/-- `lem:print`(b), paper/paper.tex: every walk reuses the original normalized atom and decomposes it before its coordinate pullback. -/
noncomputable def callMomentOccurrences (B : ℕ) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4) :
    SignedOccurrenceList ((Builder.star c hs).SideL → Bool) ((Builder.star c hs).SideR → Bool) :=
  Cells.compiledTable B
    (fun _ => Cells.walkAtoms (m := 4) (callAtoms c))
    (fun i => Cells.walkCoords (Builder.star c hs) (by norm_num : 0 < 4)
      (callPatterns c hs (indexedWalk hs.seedParameters.N i)))
    (fun i => callMomentFormula c hs w (indexedWalk hs.seedParameters.N i) j f sigma)

/-- `lem:print`(b), paper/paper.tex: the signed original-child list equals the actual formula sum, with no witness-honesty assumption. -/
theorem callMomentOccurrences_value (B : ℕ) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4)
    (hB : ∀ i, GateBits B (callAtoms c i)) (z : Fin (2 ^ (c.n-p.k))) :
    (callMomentOccurrences B c hs w j f sigma).value
      ((Builder.star c hs).leftPart (Builder.center c hs w z))
      ((Builder.star c hs).rightPart (Builder.center c hs w z)) =
    ∑ walk : Cycle.Walk hs.seedParameters.N 4,
      (callMomentFormula c hs w walk j f sigma).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
          (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z))) := by
  rw [callMomentOccurrences, Cells.compiledTable_value]
  · exact (finFunctionFinEquiv.symm.sum_comp (fun walk : Cycle.Walk hs.seedParameters.N 4 =>
      (callMomentFormula c hs w walk j f sigma).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
          (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z)))))
  · intro walk i
    exact hB (finProdFinEquiv.symm i).2

/-- `lem:print`(b), paper/paper.tex: exactly the paper's original-child count controls the complete table. -/
theorem callMomentOccurrences_length (B D Uocc : ℕ) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4)
    (hn : 0 < c.n) (hB : ∀ i, GateBits B (callAtoms c i))
    (hD : 16*p.Xmax+8*p.k ≤ D)
    (hU : 1+(17*(Builder.allGates c).length)*Cells.childCap c.n B ≤ Uocc) :
    (callMomentOccurrences B c hs w j f sigma).length ≤ hs.seedParameters.N^8 * Uocc^D := by
  apply Cells.compiledTable_length hn B D Uocc
  · intro walk i
    exact hB (finProdFinEquiv.symm i).2
  · intro i
    exact (callMomentFormula_degree c hs w _ j f sigma).trans hD
  · exact hU

/-- `eq:testE` and `lem:print`(b), paper/paper.tex: a single original-child table has the exact complete digit moment at every column. -/
theorem callDigitOccurrences_value (B : ℕ) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (sigma : Cycle.SignPattern 4) (r : Fin (p.J-1+1))
    (hB : ∀ i, GateBits B (callAtoms c i)) (z : Fin (2 ^ (c.n-p.k))) :
    (callMomentOccurrences B c hs w j (callDigitWeights c hs w j r) sigma).value
      ((Builder.star c hs).leftPart (Builder.center c hs w z))
      ((Builder.star c hs).rightPart (Builder.center c hs w z)) =
      Walks.maskedMoment (4*p.k)
        (fun walk : Walks.StructuralWalk (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural =>
          Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
            (Builder.columnData c hs w z).X walk.val)
        (fun walk => (Builder.columnData c hs w z).E j sigma walk.val r) := by
  rw [callMomentOccurrences_value B c hs w j _ sigma hB z, callDigitMoment_sum]

/-- `eq:testPhi` and `lem:print`(b), paper/paper.tex: a single original-child table has the exact complete final-error moment at every column. -/
theorem callFinalOccurrences_value (B : ℕ) (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (sigma : Cycle.SignPattern 4)
    (hB : ∀ i, GateBits B (callAtoms c i)) (z : Fin (2 ^ (c.n-p.k))) :
    (callMomentOccurrences B c hs w j (callFinalWeights c p w j) sigma).value
      ((Builder.star c hs).leftPart (Builder.center c hs w z))
      ((Builder.star c hs).rightPart (Builder.center c hs w z)) =
      Walks.maskedMoment (4*p.k)
        (fun walk : Walks.StructuralWalk (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural =>
          Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
            (Builder.columnData c hs w z).X walk.val)
        (fun walk => (Builder.columnData c hs w z).phi (by norm_num : 0 < 4) j sigma walk.val) := by
  rw [callMomentOccurrences_value B c hs w j _ sigma hB z, callFinalMoment_sum]

end NearQuarticWires.StagePrint
