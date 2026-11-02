import Proof.Quartic.StageCertNative.PriceBasic
import Proof.Quartic.StageCertSourceBounds.Expansion

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

/-- `prop:time`, paper/paper.tex: the exact
physical guarded-tuple source retains its actual occurrence factor,
which is below one full selected complete moment degree. -/
theorem price_sourceBudget (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>r.moment.sourceBudget) 1 := by
  refine ⟨momentSourcePriceCoefficient B1 B2,momentSourcePriceExponent B1 B2,fun r=>?_⟩
  have hG : (Builder.allGates r.moment.call).length≤r.moment.selected.1.Uocc := by
    have hh:=r.moment.source_occurrence_guard
    omega
  have hX : r.moment.selected.1.Xmax≤r.moment.packet.degree := by
    change r.moment.selected.1.Xmax≤16*r.moment.selected.1.Xmax+8*r.moment.selected.1.k
    omega
  have hp : (Builder.allGates r.moment.call).length^r.moment.selected.1.Xmax≤
      r.moment.selected.1.Uocc^(1*r.moment.packet.degree) :=
    (Nat.pow_le_pow_left hG _).trans
      (Nat.pow_le_pow_right (job_occurrence_pos r) (by omega))
  exact r.moment.sourceBudget_arity.trans (Nat.mul_le_mul_left _ hp)

noncomputable def actualSourceSize {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  (formulaWord ⟨r.moment.packet.arity,r.moment.formula⟩).length+
    r.moment.formula.size+r.moment.formula.weight+1

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete literal signed codec, syntax and source
weight obey the selected occurrence degree on every proposed witness. -/
theorem price_actualSourceSize (B1 B2 : ℕ) : JobPrice (@actualSourceSize B1 B2) 1 := by
  refine ⟨StageCertSourceBounds.actualFormulaCoefficient B1 B2,
    StageCertSourceBounds.actualFormulaExponent B1 B2,fun r=>?_⟩
  have hbase : 17*(Builder.allGates r.moment.call).length+1≤r.moment.selected.1.Uocc := by
    have hh:=r.moment.source_occurrence_guard
    omega
  have hk:=job_dimension_pos r
  have hX : r.moment.selected.1.Xmax+1≤r.moment.packet.degree := by
    change r.moment.selected.1.Xmax+1≤16*r.moment.selected.1.Xmax+8*r.moment.selected.1.k
    omega
  have hp : (17*(Builder.allGates r.moment.call).length+1)^(r.moment.selected.1.Xmax+1)≤
      r.moment.selected.1.Uocc^(1*r.moment.packet.degree) :=
    (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (job_occurrence_pos r) (by omega))
  exact (StageCertSourceBounds.actual_formula_source_arity r.moment).trans
    (Nat.mul_le_mul_left _ hp)

noncomputable def expansionCost {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  NearCubicGates.Close.Expand.expansionMachine.budget ⟨r.moment.packet.arity,r.moment.formula⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the concrete exact expansion has a per-term cubic
degree price before the actual whole-term loop multiplies its clock.
This bound does not spend the original-column reserve prematurely. -/
theorem price_expansionCost (B1 B2 : ℕ) : JobPrice (@expansionCost B1 B2) 3 := by
  refine ⟨StageCertSourceBounds.actualExpansionCoefficient B1 B2,
    StageCertSourceBounds.actualExpansionExponent B1 B2,fun r=>?_⟩
  let m:=r.moment
  let V:=17*(Builder.allGates m.call).length
  let D:=m.packet.degree
  let A:=StageCertSourceBounds.actualFormulaCoefficient B1 B2
  let d:=StageCertSourceBounds.actualFormulaExponent B1 B2
  have hb:=NearCubicGates.Close.Expand.Layout.budget_le (⟨V,m.formula⟩:FormulaReq)
  have hdegree : (V+2)^(2*m.formula.degree+3)≤(V+2)^(2*D+3) :=
    Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 m.formula_degree) 3)
  have hshape:=Cells.ParameterArithmetic.expansion_cost_factor_bound m.call.n V D m.selected.1.Xmax
    A d ((formulaWord ⟨V,m.formula⟩).length+m.formula.size+m.formula.weight+1)
    (StageCertSourceBounds.actual_pool_arity_le m)
    (by dsimp only [D,StageFormulaMetadata.RawWalkPacket.degree];change 16*m.selected.1.Xmax≤16*m.selected.1.Xmax+8*m.selected.1.k;omega)
    (StageCertSourceBounds.actual_formula_source_arity m)
  have hconcrete : expansionCost r≤
      (10^11*A^8*35^8*36^3)*(m.call.n+1)^(8*d+44)*(V+2)^(3*D) := by
    calc
      _≤10^11*(V+2)^(2*m.formula.degree+3)*
        ((formulaWord ⟨V,m.formula⟩).length+m.formula.size+m.formula.weight+1)^8 := hb
      _≤10^11*((V+2)^(2*D+3)*
        ((formulaWord ⟨V,m.formula⟩).length+m.formula.size+m.formula.weight+1)^8) :=
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdegree)).trans_eq (by ring)
      _≤10^11*((A^8*35^8*36^3)*(m.call.n+1)^(8*d+44)*(V+2)^(3*D)) :=
        Nat.mul_le_mul_left _ hshape
      _=_ := by ring
  exact hconcrete.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left m.source_occurrence_guard _))

end NearQuarticWires.StageCertNative
