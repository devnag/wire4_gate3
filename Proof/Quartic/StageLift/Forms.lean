import Proof.Quartic.StagePrint.BuilderErrors

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearQuarticWires

/-- `lem:residue` and `lem:print`, paper/paper.tex: the exact digit and score forms on the unchanged
seventeen-role original occurrence pool. -/
noncomputable def callResidueForm (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (sigma : Cycle.SignPattern 4) (index : Fin 2 × Option (Fin (p.J - 1 + 1))) :
    Formula (17 * (Builder.allGates c).length) := by
  classical
  exact if index.1 ∈ Builder.circuitSet c then
    match index.2 with
    | some r => StagePrint.callWalkFormula c index.1
        (StagePrint.callDigitWeights c hs w index.1 r) sigma
    | none => StagePrint.callWalkFormula c index.1 (fun _ => 1) sigma
  else .const 0

/-- `lem:print`, paper/paper.tex: all literal
residue forms are linear in the physical original atom pool. -/
theorem callResidueForm_degree (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (sigma : Cycle.SignPattern 4) (index : Fin 2 × Option (Fin (p.J - 1 + 1))) :
    (callResidueForm c hs w sigma index).degree ≤ 1 := by
  unfold callResidueForm
  split
  · cases index.2 <;> exact StagePrint.callWalkFormula_degree _ _ _ _
  · exact Nat.zero_le _

/-- `lem:residue` and `lem:print`, paper/paper.tex: each generated form equals the actual column's
digit or score function, including absent circuits. -/
theorem callResidueForm_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (sigma : Cycle.SignPattern 4) (index : Fin 2 × Option (Fin (p.J - 1 + 1))) :
    (callResidueForm c hs w sigma index).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (StagePrint.callPatterns c hs walk) (StagePrint.callAtoms c) (Builder.center c hs w z))) =
      (Builder.cellCall c hs w).residueForms z sigma walk index := by
  classical
  rcases index with ⟨j, index⟩
  by_cases hj : j ∈ Builder.circuitSet c
  · cases index with
    | none =>
        simp only [callResidueForm, hj, if_true]
        unfold Algorithm.CellCall.residueForms
        change _ = if j ∈ Builder.circuitSet c then
          (Builder.columnData c hs w z).Y Algorithm.traceOrder_pos j sigma walk else 0
        rw [if_pos hj]
        change (StagePrint.callWalkFormula c j (fun _ => 1) sigma).eval _ =
          (Builder.columnData c hs w z).Y Algorithm.traceOrder_pos j sigma walk
        rw [StagePrint.callWalkFormula_eval]
        simpa only [one_mul, Builder.cellCall] using
          (Builder.walkSum_eq_sum_contribution c hs w z j sigma walk).symm
    | some r =>
        simp only [callResidueForm, hj, if_true]
        unfold Algorithm.CellCall.residueForms
        change _ = if j ∈ Builder.circuitSet c then
          (Builder.columnData c hs w z).E j sigma walk r else 0
        rw [if_pos hj]
        change (StagePrint.callWalkFormula c j (StagePrint.callDigitWeights c hs w j r) sigma).eval _ =
          (Builder.columnData c hs w z).E j sigma walk r
        exact StagePrint.callDigitFormula_eval c hs w z walk j sigma r
  · simp [callResidueForm, Algorithm.CellCall.residueForms, Builder.cellCall, Builder.columnData, hj,
      Formula.eval]

end NearQuarticWires.StageLift
