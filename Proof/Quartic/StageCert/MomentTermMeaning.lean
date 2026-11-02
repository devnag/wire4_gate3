import Proof.Quartic.StageCert.MomentIndexEquiv
import Proof.Quartic.StageCert.MomentWitnessDock

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the actual
source term is evaluated on the original seventeen-role raw atom
pool at the original witness's canonical column center. -/
noncomputable def MomentRequest.termAtoms {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (z : Fin (2^(r.call.n-r.selected.1.k))) : Fin (17*(Builder.allGates r.call).length)→ℤ :=
  boolPoint (Cells.walkAtomPoint (Builder.star r.call r.rules) (by decide : 0<4)
    (StagePrint.callPatterns r.call r.rules r.walk) (StagePrint.callAtoms r.call)
    (Builder.center r.call r.rules r.witness z))

/-- `lem:print`, paper/paper.tex: exact signed
evaluation of the literal physically emitted source tree. -/
noncomputable def MomentRequest.termValue {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (z : Fin (2^(r.call.n-r.selected.1.k))) : ℤ := r.formula.eval (r.termAtoms z)

/-- `eq:testE` and `lem:print`, paper/paper.tex: each actual digit source term is its complete original
Builder masked moment summand, before any strict test passes. -/
theorem MomentRequest.digit_term_value {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (code : Fin 256) (row : Fin (r.selected.1.J-1+1))
    (ht : r.test=.digit j code row) (z : Fin (2^(r.call.n-r.selected.1.k))) :
    r.termValue z=
      (StagePrint.callMomentFormula r.call r.rules r.retainedWitness r.walk j
        (StagePrint.callDigitWeights r.call r.rules r.retainedWitness j row)
        (StageCertTests.patternOfCode code.val)).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star r.call r.rules) (by decide : 0<4)
          (StagePrint.callPatterns r.call r.rules r.walk) (StagePrint.callAtoms r.call)
          (Builder.center r.call r.rules r.retainedWitness z))) := by
  unfold MomentRequest.termValue MomentRequest.termAtoms
  simp only [MomentRequest.formula,ht]
  rw [source_digit_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j row code.val,
    tupleCallMomentFormula_eval,r.retained_center_eq]

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: exact final-error terms retain all original offsets
and the complete proposed child chain on bad columns. -/
theorem MomentRequest.final_term_value {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (j : Fin 2) (code : Fin 256) (ht : r.test=.finalError j code)
    (z : Fin (2^(r.call.n-r.selected.1.k))) :
    r.termValue z=
      (StagePrint.callMomentFormula r.call r.rules r.retainedWitness r.walk j
        (StagePrint.callFinalWeights r.call r.selected.1 r.retainedWitness j)
        (StageCertTests.patternOfCode code.val)).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star r.call r.rules) (by decide : 0<4)
          (StagePrint.callPatterns r.call r.rules r.walk) (StagePrint.callAtoms r.call)
          (Builder.center r.call r.rules r.retainedWitness z))) := by
  unfold MomentRequest.termValue MomentRequest.termAtoms
  simp only [MomentRequest.formula,ht]
  rw [source_final_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j code.val,
    tupleCallMomentFormula_eval,r.retained_center_eq]

/-- `eq:testX` and `lem:print`, paper/paper.tex: one literal population term is the structural
zero/one coefficient times the original population's even power. -/
theorem MomentRequest.population_term_value {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (ht : r.test=.population) (z : Fin (2^(r.call.n-r.selected.1.k))) :
    r.termValue z=
      (if (Builder.columnData r.call r.rules r.witness z).structural
        (Cycle.edge (by decide : 0<4) r.walk 0) then (1:ℤ) else 0)*
      ((Builder.columnData r.call r.rules r.witness z).X
        (Cycle.edge (by decide : 0<4) r.walk 0) : ℤ)^(2*r.selected.1.k) := by
  unfold MomentRequest.termValue MomentRequest.termAtoms
  simp only [MomentRequest.formula,ht,StagePrint.selectedPopulationMomentFormula,Formula.eval]
  rw [←r.retained_center_eq z]
  change (if StagePrint.callStructural r.call r.rules r.walk 0 then (1:ℤ) else 0)*
    (StagePrint.selectedPopulationFormula (by decide : 0<4)
      (Builder.selection r.call (p:=r.selected.1) r.retainedWitness) 0).eval _ ^
      (2*r.selected.1.k)=_
  rw [StagePrint.callPopulation_eval,r.retained_columnData_eq]
  rfl

end NearQuarticWires.StageCert.Tokens
