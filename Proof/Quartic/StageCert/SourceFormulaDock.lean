import Proof.Quartic.StageCert.SourceCircuitDock
import Proof.Quartic.StageCertTests.PatternParity

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Interfaces

/-- `eq:testE` and `lem:print`, paper/paper.tex: the complete physically emitted digit AST is exactly the
original Builder walk formula, not merely a passing-column approximation. -/
theorem source_digit_formula_eq_builder (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (j : Fin 2) (r : Fin (p.J-1+1)) (code : ℕ) :
    sourceDigitWalkFormula (Builder.allGates c).length r.val p.J p.k j.val
      c.first.gates.length code bits p.factors=
      StagePrint.callWalkFormula c j (StagePrint.callDigitWeights c hs bits j r)
        (StageCertTests.patternOfCode code) := by
  change Cells.pooledWalkFormula (by decide : 0<4) (sourceDigitGlobalWeights c p bits j r.val)
    (fun e=>Cycle.signValue (code.testBit e.val))=_
  rw [show sourceDigitGlobalWeights c p bits j r.val=
      StagePrint.circuitWeights c j (StagePrint.callDigitWeights c hs bits j r) by
    funext g
    exact source_digit_global_eq_builder c hs bits j r g]
  rfl

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the complete final-error AST agrees exactly with its
original signed walk formula on every formal atom assignment. -/
theorem source_final_formula_eq_builder (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (code : ℕ) :
    sourceFinalWalkFormula (Builder.allGates c).length p.J p.k p.M1 p.A j.val
      c.first.gates.length code bits=
      StagePrint.callWalkFormula c j (StagePrint.callFinalWeights c p bits j)
        (StageCertTests.patternOfCode code) := by
  change Cells.pooledWalkFormula (by decide : 0<4) (sourceFinalGlobalWeights c p bits j)
    (fun e=>Cycle.signValue (code.testBit e.val))=_
  rw [show sourceFinalGlobalWeights c p bits j=
      StagePrint.circuitWeights c j (StagePrint.callFinalWeights c p bits j) by
    funext g
    exact source_final_global_eq_builder c p bits j g]
  rfl

end NearQuarticWires.StageCert.Tokens
