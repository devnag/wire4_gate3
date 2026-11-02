import Proof.Quartic.Builder.CellCall
import Proof.Quartic.StagePrint.SelectedMoments

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator

/-- `sec:cells` and `lem:print`, paper/paper.tex: the physical original occurrence list, with no duplicate removal. -/
def callAtoms (c : Call) : Fin (Builder.allGates c).length → NormalizedThresholdGate c.n :=
  fun i => (Builder.allGates c)[i.val]

/-- `lem:print`, paper/paper.tex: the actual indexed walk's star error pattern at each vertex. -/
noncomputable def callPatterns (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p)
    (walk : Cycle.Walk hs.seedParameters.N 4) : Fin 8 → (Builder.star c hs).Errors :=
  fun l => Builder.pattern c hs (walk l)

/-- `eq:testX` and `lem:print`(c), paper/paper.tex: the formula's selected population is exactly the column data consulted by certification. -/
theorem callPopulation_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4) (e : Fin 8) :
    (selectedPopulationFormula (by norm_num : 0 < 4) (Builder.selection c (p := p) w) e).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4) (callPatterns c hs walk)
        (callAtoms c) (Builder.center c hs w z))) =
      (((Builder.columnData c hs w z).X (Cycle.edge (by norm_num : 0 < 4) walk e)) : ℤ) := by
  rw [selectedPopulationFormula_eval]
  have he : Cycle.edge (by norm_num : 0 < 4) walk e =
      (walk (Cells.leftSlot (by norm_num : 0 < 4) e), walk (Cells.rightSlot (by norm_num : 0 < 4) e)) :=
    (Cells.slots_cellOf (by norm_num : 0 < 4) walk e).symm
  rw [he]
  rfl

/-- `def:mask` and `lem:print`, paper/paper.tex: the active-set cardinality is the actual witness-selected X value. -/
theorem callActive_card (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4) (e : Fin 8) :
    (selectedActive (Builder.star c hs) (by norm_num : 0 < 4) (callPatterns c hs walk) (callAtoms c)
      (Builder.center c hs w z) (Builder.selection c (p := p) w) e).card =
      (Builder.columnData c hs w z).X (Cycle.edge (by norm_num : 0 < 4) walk e) := by
  rw [selectedActive_card]
  have he : Cycle.edge (by norm_num : 0 < 4) walk e =
      (walk (Cells.leftSlot (by norm_num : 0 < 4) e), walk (Cells.rightSlot (by norm_num : 0 < 4) e)) :=
    (Cells.slots_cellOf (by norm_num : 0 < 4) walk e).symm
  rw [he]
  rfl

/-- `eq:testE`, `eq:testPhi` and `lem:print`(b), paper/paper.tex: the formula's literal mask polynomial agrees with the actual column mask before any strict test is passed. -/
theorem callMask_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4) (e : Fin 8) :
    (selectedMaskFormula (by norm_num : 0 < 4) (Builder.selection c (p := p) w)
      ((Builder.columnData c hs w z).structural (Cycle.edge (by norm_num : 0 < 4) walk e)) e p.tau p.Xmax).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4) (callPatterns c hs walk)
        (callAtoms c) (Builder.center c hs w z))) =
      Mask.maskPolyEval ((Builder.columnData c hs w z).structural (Cycle.edge (by norm_num : 0 < 4) walk e)) p.tau p.Xmax
        ((Builder.columnData c hs w z).X (Cycle.edge (by norm_num : 0 < 4) walk e)) := by
  rw [selectedMaskFormula_eval_poly, callActive_card]

end NearQuarticWires.StagePrint
