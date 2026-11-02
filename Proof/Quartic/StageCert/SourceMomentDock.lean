import Proof.Quartic.StageCert.SourceFormulaDock
import Proof.Quartic.StageCert.FinalMoment
import Proof.Quartic.StageLift.FormulaSize

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: physical tuple
mask serialization uses exactly the shared original walk-product AST. -/
theorem completeWalkMaskFormula_eq_masks (G tau X k : ℕ) (bits : List Bool)
    (structural : Fin 8→Bool) :
    completeWalkMaskFormula G tau X k bits structural=
      Cells.walkMaskFormula (fun edge=>tupleMaskFormula (structural edge)
        (StagePrint.selectedSquare (by decide : 0<4)
          (fun i : Fin G=>bits.getD (k+i.val) false) edge) tau X) := by
  unfold completeWalkMaskFormula selectedWalkMasks Cells.walkMaskFormula
  rw [StageLift.formula_prodList_eq]
  simp only [List.map_ofFn,Function.comp_def]

/-- `eq:testE` and `lem:print`, paper/paper.tex: the actual emitted complete digit moment is the literal
original tuple-source Builder moment, on every proposed witness. -/
theorem source_digit_moment_eq_tuple (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (r : Fin (p.J-1+1)) (code : ℕ) :
    sourceDigitMomentFormula (Builder.allGates c).length r.val p.J p.k j.val
      c.first.gates.length code p.tau p.Xmax bits p.factors (StagePrint.callStructural c hs walk)=
      tupleCallMomentFormula c hs bits walk j (StagePrint.callDigitWeights c hs bits j r)
        (StageCertTests.patternOfCode code) := by
  unfold sourceDigitMomentFormula
  rw [source_digit_formula_eq_builder c hs bits j r code,completeWalkMaskFormula_eq_masks]
  rfl

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the actual emitted complete final-error moment is
the original tuple-source Builder moment, including all signed offsets. -/
theorem source_final_moment_eq_tuple (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2) (code : ℕ) :
    sourceFinalMomentFormula (Builder.allGates c).length p.J p.k p.M1 p.A j.val
      c.first.gates.length code p.tau p.Xmax bits (StagePrint.callStructural c hs walk)=
      tupleCallMomentFormula c hs bits walk j (StagePrint.callFinalWeights c p bits j)
        (StageCertTests.patternOfCode code) := by
  unfold sourceFinalMomentFormula
  rw [source_final_formula_eq_builder c p bits j code,completeWalkMaskFormula_eq_masks]
  rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: actual digit token generation preserves the exact
original formal mass used by the native signed-coefficient width bound. -/
theorem source_digit_moment_mass (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2)
    (r : Fin (p.J-1+1)) (code : ℕ) :
    (sourceDigitMomentFormula (Builder.allGates c).length r.val p.J p.k j.val
      c.first.gates.length code p.tau p.Xmax bits p.factors (StagePrint.callStructural c hs walk)).mass=
      (StagePrint.callMomentFormula c hs bits walk j (StagePrint.callDigitWeights c hs bits j r)
        (StageCertTests.patternOfCode code)).mass := by
  rw [source_digit_moment_eq_tuple,tupleCallMomentFormula_mass]

/-- `lem:print` and `prop:time`, paper/paper.tex: actual final-error output has the original formal
mass on all columns, without assuming any strict test has passed. -/
theorem source_final_moment_mass (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (j : Fin 2) (code : ℕ) :
    (sourceFinalMomentFormula (Builder.allGates c).length p.J p.k p.M1 p.A j.val
      c.first.gates.length code p.tau p.Xmax bits (StagePrint.callStructural c hs walk)).mass=
      (StagePrint.callMomentFormula c hs bits walk j (StagePrint.callFinalWeights c p bits j)
        (StageCertTests.patternOfCode code)).mass := by
  rw [source_final_moment_eq_tuple,tupleCallMomentFormula_mass]

end NearQuarticWires.StageCert.Tokens
