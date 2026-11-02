import Proof.Quartic.StageLiftTokens.ScoreWalkForm
import Proof.Quartic.StageCert.SourceFormulaDock

/-!
# Exact score formula identity

`lem:residue` and `lem:print`, paper/paper.tex: the serialized unit-coefficient Y score is exactly
the Builder formula on the unchanged concatenated occurrence bank.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Interfaces StageCert.Tokens

def sourceScoreWeights (c : Call) (j : Fin 2)
    (g : Fin (Builder.allGates c).length) : ℤ :=
  (selectedSummand j.val c.first.gates.length g.val 1 : ℤ)

theorem source_score_weights_eq_builder (c : Call) (j : Fin 2)
    (g : Fin (Builder.allGates c).length) :
    sourceScoreWeights c j g=StagePrint.circuitWeights c j (fun _=>1) g := by
  unfold sourceScoreWeights selectedSummand StagePrint.circuitWeights
  split_ifs <;> rfl

theorem source_score_formula_eq_builder (c : Call) (j : Fin 2) (code : ℕ) :
    sourceScoreWalkFormula (Builder.allGates c).length j.val c.first.gates.length code=
      StagePrint.callWalkFormula c j (fun _=>1) (StageCertTests.patternOfCode code) := by
  change Cells.pooledWalkFormula (by decide : 0<4) (sourceScoreWeights c j)
    (fun e=>Cycle.signValue (code.testBit e.val))=_
  rw [show sourceScoreWeights c j=StagePrint.circuitWeights c j (fun _=>1) by
    funext g
    exact source_score_weights_eq_builder c j g]
  rfl

end NearQuarticWires.StageLiftTokens
