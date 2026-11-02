import Proof.Quartic.StageCert.TupleMass
import Proof.Quartic.StagePrint.BuilderMoments

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator

/-- `lem:print`(b), paper/paper.tex: the actual
tuple-source mask used by each fixed walk edge in the moment request. -/
noncomputable def tupleCallMomentFormula (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4) :
    Formula (17*(Builder.allGates c).length) :=
  Cells.momentWalkFormula
    (fun edge=>tupleMaskFormula (StagePrint.callStructural c hs walk edge)
      (StagePrint.selectedSquare (by decide : 0<4) (Builder.selection c (p := p) w) edge)
      p.tau p.Xmax)
    (StagePrint.callWalkFormula c j f sigma) p.k

/-- `lem:print`(b), paper/paper.tex: the complete
actual tuple-source moment has the paper's unchanged native degree. -/
theorem tupleCallMomentFormula_degree (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4) :
    (tupleCallMomentFormula c hs w walk j f sigma).degree≤16*p.Xmax+8*p.k := by
  apply Cells.momentWalkFormula_degree
  · intro edge
    exact tupleMaskFormula_degree_le _ _ _ _ (fun g=>StagePrint.selectedSquare_degree _ _ _ g)
  · exact StagePrint.callWalkFormula_degree c j f sigma

/-- `lem:print`(b), paper/paper.tex: actual tuple
serialization changes no moment value on any formal integer assignment,
including all original bad columns and all proposed chain witnesses. -/
theorem tupleCallMomentFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4)
    (point : Fin (17*(Builder.allGates c).length)→ℤ) :
    (tupleCallMomentFormula c hs w walk j f sigma).eval point=
      (StagePrint.callMomentFormula c hs w walk j f sigma).eval point := by
  simp only [tupleCallMomentFormula,StagePrint.callMomentFormula,Cells.momentWalkFormula_eval]
  congr 1
  apply Finset.prod_congr rfl
  intro edge _
  exact tupleMaskFormula_eval _ _ _ _ point

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal product constructor's mass is the product of
its actual integer factor masses. -/
theorem formulaProdList_mass {V : ℕ} (fs : List (Formula V)) :
    (Formula.prodList fs).mass=(fs.map Formula.mass).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [Formula.prodList,Formula.mass,ih]

/-- `lem:print` and `prop:time`, paper/paper.tex: executable tuple enumeration leaves the exact original
moment mass unchanged. Native coefficient widths therefore use the same
polynomial logarithmic mass bound, independently of every certificate. -/
theorem tupleCallMomentFormula_mass (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (f : Fin (Builder.occurrences c j)→ℤ) (sigma : Cycle.SignPattern 4) :
    (tupleCallMomentFormula c hs w walk j f sigma).mass=
      (StagePrint.callMomentFormula c hs w walk j f sigma).mass := by
  unfold tupleCallMomentFormula StagePrint.callMomentFormula Cells.momentWalkFormula
  simp only [Formula.mass]
  congr 1
  unfold Cells.walkMaskFormula
  rw [formulaProdList_mass,formulaProdList_mass]
  simp only [List.map_ofFn,List.prod_ofFn,Function.comp_def]
  apply Finset.prod_congr rfl
  intro edge _
  exact tupleMaskFormula_mass _ _ _ _

end NearQuarticWires.StageCert
