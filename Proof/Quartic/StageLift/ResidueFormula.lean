import Proof.Quartic.StageLift.Fermat
import Proof.Quartic.StageLift.ReduceFormula
import Proof.Quartic.StagePrint.BuilderMoments
import Proof.Quartic.Greedy.Child

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearQuarticWires
open scoped BigOperators

/-- `lem:residue`, paper/paper.tex: the exact
target vector is independent of the column being printed. -/
noncomputable def callResidueTarget (c : Call) (p : Cells.Parameters) (prime : ℕ)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ)
    (index : Fin 2 × Option (Fin (p.J - 1 + 1))) : ℤ := by
  classical
  exact if index.1 ∈ Builder.circuitSet c then
    match index.2 with
    | some r => digits index.1 r % (prime : ℤ)
    | none => residues index.1
  else 0

/-- `lem:print` and `lem:residue`, paper/paper.tex: one actual walk's weighted selected-mask and amplified
residue formula on the original shared atom pool. -/
noncomputable def callResidueWalkFormula (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ) : Formula (17 * (Builder.allGates c).length) :=
  .mul (.const weight) (.mul
    (Cells.walkMaskFormula (fun e => StagePrint.selectedMaskFormula (by norm_num : 0 < 4)
      (Builder.selection c (p := p) w) (StagePrint.callStructural c hs walk e) e p.tau p.Xmax))
    (Formula.amp p.e (indexedFermatFormula prime (callResidueForm c hs w sigma)
      (callResidueTarget c p prime digits residues))))

/-- `lem:print` and `lem:residue`, paper/paper.tex: the concrete formula equals the literal printed-count
walk summand on every original center, before any certification test. -/
theorem callResidueWalkFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (sigma : Cycle.SignPattern 4) (prime : ℕ)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    (callResidueWalkFormula c hs w walk sigma prime digits residues weight).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (StagePrint.callPatterns c hs walk) (StagePrint.callAtoms c) (Builder.center c hs w z))) =
      weight * Walks.walkMaskPoly Algorithm.traceOrder_pos (Builder.columnData c hs w z).structural
        p.tau p.Xmax (Builder.columnData c hs w z).X walk *
        NearCubicGates.ResidueCounts.liftedIndicator prime p.e
          ((Builder.cellCall c hs w).residueForms z sigma walk)
          ((Builder.cellCall c hs w).residueTarget z prime digits residues) := by
  rw [callResidueWalkFormula, Formula.eval, Formula.eval, Formula.eval,
    Cells.walkMaskFormula_eval, Formula.eval_amp, indexedFermatFormula_eval]
  have hmask : (∏ e : Fin 8,
      (StagePrint.selectedMaskFormula (by norm_num : 0 < 4) (Builder.selection c (p := p) w)
        (StagePrint.callStructural c hs walk e) e p.tau p.Xmax).eval
        (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
          (StagePrint.callPatterns c hs walk) (StagePrint.callAtoms c) (Builder.center c hs w z)))) =
      Walks.walkMaskPoly Algorithm.traceOrder_pos (Builder.columnData c hs w z).structural
        p.tau p.Xmax (Builder.columnData c hs w z).X walk := by
    apply Finset.prod_congr rfl
    intro e _
    exact StagePrint.callMask_eval c hs w z walk e
  rw [hmask]
  simp_rw [callResidueForm_eval]
  have htarget : callResidueTarget c p prime digits residues =
      (Builder.cellCall c hs w).residueTarget z prime digits residues := by
    funext ⟨j, i⟩
    cases i <;> by_cases hj : j ∈ Builder.circuitSet c <;>
      simp [callResidueTarget, Algorithm.CellCall.residueTarget, Builder.cellCall, Builder.columnData, hj]
  rw [htarget]
  simp only [NearCubicGates.ResidueCounts.liftedIndicator, mul_assoc]
  congr 3

/-- `lem:print`, paper/paper.tex: the literal
weighted residue formula obeys the unchanged quartic degree expression. -/
theorem callResidueWalkFormula_degree (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ)
    (residues : Fin 2 → ℤ) (weight : ℤ) :
    (callResidueWalkFormula c hs w walk sigma prime digits residues weight).degree ≤
      16 * p.Xmax + (2 * p.e - 1) * (2 * (p.J - 1 + 2)) * (prime - 1) := by
  simp only [callResidueWalkFormula, Formula.degree, zero_add]
  apply Nat.add_le_add
  · exact Cells.walkMaskFormula_degree _ (fun e => StagePrint.selectedMaskFormula_degree
      (by norm_num : 0 < 4) _ _ e _ _)
  · apply (Formula.degree_amp_le _ _).trans
    have h := Nat.mul_le_mul_left (2 * p.e - 1)
      (indexedFermatFormula_degree prime (callResidueForm c hs w sigma)
        (callResidueTarget c p prime digits residues) (callResidueForm_degree c hs w sigma))
    simpa only [Nat.mul_assoc] using h

end NearQuarticWires.StageLift
