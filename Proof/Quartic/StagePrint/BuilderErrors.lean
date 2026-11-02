import Proof.Quartic.StagePrint.BuilderWeights
import Proof.Quartic.Builder.Localize

set_option autoImplicit false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator

/-- `sec:walks` and `lem:print`, paper/paper.tex: the exact occurrence coefficients of any proposed digit. -/
noncomputable def callDigitWeights (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (r : Fin (p.J - 1 + 1)) (t : Fin (Builder.occurrences c j)) : ℤ :=
  NearCubicGates.CountingCore.proposedDigit
    (fun i => ((Builder.algorithmParameters c hs).rate i : ℤ))
    (fun i => Builder.chainBit c (p := p) w j i t) r.val

/-- `sec:walks` and `lem:print`, paper/paper.tex: the final-error coefficients retain the complete residual with its literal scale A. -/
def callFinalWeights (c : Call) (p : Cells.Parameters) (w : List Bool)
    (j : Fin 2) (t : Fin (Builder.occurrences c j)) : ℤ :=
  (p.M1 : ℤ) * Builder.chainBit c (p := p) w j (p.J - 1) t - (p.A : ℤ)

/-- `eq:testE` and `lem:print`(b), paper/paper.tex: a linear digit formula is exact for every witness, before certification. -/
theorem callDigitWeights_sum (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (j : Fin 2) (sigma : Cycle.SignPattern 4) (r : Fin (p.J - 1 + 1)) :
    (∑ t, callDigitWeights c hs w j r t * Builder.contribution c hs w z j t sigma walk) =
      (Builder.columnData c hs w z).E j sigma walk r := by
  cases hr : r.val with
  | zero =>
    simp only [callDigitWeights, Walks.WalkData.E, hr,
      NearCubicGates.CountingCore.proposedDigit, Builder.columnData]
  | succ i =>
    simp only [callDigitWeights, hr, NearCubicGates.CountingCore.proposedDigit,
      Walks.WalkData.E, Builder.columnData, sub_mul, mul_assoc, Finset.sum_sub_distrib,
      Finset.mul_sum]

/-- `eq:testPhi` and `lem:print`(b), paper/paper.tex: the final-error formula keeps all original occurrences, including unselected ones. -/
theorem callFinalWeights_sum (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (j : Fin 2) (sigma : Cycle.SignPattern 4) :
    (∑ t, callFinalWeights c p w j t * Builder.contribution c hs w z j t sigma walk) =
      (Builder.columnData c hs w z).phi (by norm_num : 0 < 4) j sigma walk := by
  rw [Walks.WalkData.phi]
  have hy := Builder.walkSum_eq_sum_contribution c hs w z j sigma walk
  change (Builder.columnData c hs w z).Y (by norm_num : 0 < 4) j sigma walk = _ at hy
  rw [hy]
  simp only [callFinalWeights, Builder.columnData, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, Finset.mul_sum]

/-- `eq:testE` and `lem:print`(b), paper/paper.tex: the actual digit is the evaluation of a degree-one pooled formula. -/
theorem callDigitFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (j : Fin 2) (sigma : Cycle.SignPattern 4) (r : Fin (p.J - 1 + 1)) :
    (callWalkFormula c j (callDigitWeights c hs w j r) sigma).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z))) =
      (Builder.columnData c hs w z).E j sigma walk r := by
  rw [callWalkFormula_eval, callDigitWeights_sum]

/-- `eq:testPhi` and `lem:print`(b), paper/paper.tex: the actual final error is the evaluation of a degree-one pooled formula. -/
theorem callFinalFormula_eval (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (z : Fin (2 ^ (c.n - p.k))) (walk : Cycle.Walk hs.seedParameters.N 4)
    (j : Fin 2) (sigma : Cycle.SignPattern 4) :
    (callWalkFormula c j (callFinalWeights c p w j) sigma).eval
      (boolPoint (Cells.walkAtomPoint (Builder.star c hs) (by norm_num : 0 < 4)
        (callPatterns c hs walk) (callAtoms c) (Builder.center c hs w z))) =
      (Builder.columnData c hs w z).phi (by norm_num : 0 < 4) j sigma walk := by
  rw [callWalkFormula_eval, callFinalWeights_sum]

end NearQuarticWires.StagePrint
