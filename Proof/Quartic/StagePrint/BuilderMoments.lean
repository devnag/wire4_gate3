import Proof.Quartic.StagePrint.BuilderErrors

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator

/-- `def:mask` and `lem:print`(b), paper/paper.tex: structural walk flags are fixed before the center assignment. -/
noncomputable def callStructural (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p)
    (walk : Cycle.Walk hs.seedParameters.N 4) (e : Fin 8) : Bool :=
  Mask.structuralMask ((Builder.star c hs).flipSet (Builder.star c hs).leftBlock)
    ((Builder.star c hs).flipSet (Builder.star c hs).rightBlock)
    (Mask.heavyCoordinates (Cells.incidence (Builder.allGates c)) p.dstar)
    (Builder.pattern c hs (Cycle.edge (by norm_num : 0 < 4) walk e).1)
    (Builder.pattern c hs (Cycle.edge (by norm_num : 0 < 4) walk e).2)

/-- `lem:print`(b), paper/paper.tex: an exact masked moment formula with arbitrary original occurrence weights. -/
noncomputable def callMomentFormula (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4) :
    Formula (17 * (Builder.allGates c).length) :=
  Cells.momentWalkFormula
    (fun e => selectedMaskFormula (by norm_num : 0 < 4) (Builder.selection c (p := p) w)
      (callStructural c hs walk e) e p.tau p.Xmax)
    (callWalkFormula c j f sigma) p.k

/-- `lem:print`(b), paper/paper.tex: the complete masked moment has the literal paper degree. -/
theorem callMomentFormula_degree (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4) :
    (callMomentFormula c hs w walk j f sigma).degree ≤ 16 * p.Xmax + 8 * p.k :=
  Cells.momentWalkFormula_degree _ _ _
    (fun e => selectedMaskFormula_degree (by norm_num : 0 < 4)
      (Builder.selection c (p := p) w) (callStructural c hs walk e) e p.tau p.Xmax)
    (callWalkFormula_degree c j f sigma)

/-- `eq:testE`, `eq:testPhi` and `lem:print`(b), paper/paper.tex: evaluation agrees with the literal column mask polynomial without assuming any certification test. -/
theorem callMomentFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j) → ℤ) (sigma : Cycle.SignPattern 4) :
    (callMomentFormula c hs w walk j f sigma).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z))) =
      Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
        (Builder.columnData c hs w z).X walk *
          (∑ t, f t * Builder.contribution c hs w z j t sigma walk) ^ (8 * p.k) := by
  rw [callMomentFormula, Cells.momentWalkFormula_eval, callWalkFormula_eval]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact callMask_eval c hs w z walk e

/-- `eq:testE` and `lem:print`(b), paper/paper.tex: each actual chain-digit summand is printed by its complete formula. -/
theorem callDigitMoment_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (sigma : Cycle.SignPattern 4) (r : Fin (p.J - 1 + 1)) :
    (callMomentFormula c hs w walk j (callDigitWeights c hs w j r) sigma).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z))) =
      Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
        (Builder.columnData c hs w z).X walk *
          (Builder.columnData c hs w z).E j sigma walk r ^ (8 * p.k) := by
  rw [callMomentFormula_eval, callDigitWeights_sum]

/-- `eq:testPhi` and `lem:print`(b), paper/paper.tex: each actual final-error summand is printed by its complete formula. -/
theorem callFinalMoment_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (sigma : Cycle.SignPattern 4) :
    (callMomentFormula c hs w walk j (callFinalWeights c p w j) sigma).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z))) =
      Walks.walkMaskPoly (by norm_num : 0 < 4) (Builder.columnData c hs w z).structural p.tau p.Xmax
        (Builder.columnData c hs w z).X walk *
          (Builder.columnData c hs w z).phi (by norm_num : 0 < 4) j sigma walk ^ (8 * p.k) := by
  rw [callMomentFormula_eval, callFinalWeights_sum]

end NearQuarticWires.StagePrint
