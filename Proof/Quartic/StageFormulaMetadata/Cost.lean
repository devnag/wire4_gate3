import Proof.Quartic.StageFormulaMetadata.Machine
import Proof.Quartic.StageFormulaMetadata.SourceCost

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires
open NearCubicGates.Close.Cells
open StageRecovery (packetCallee)

/-- `prop:time`, paper/paper.tex: the complete
physical ledger is monotone in its actual source-program clock. -/
theorem finiteBudget_mono (K : Callee) (variableCount stores : ℕ) (bits : List Bool)
    (first second : ℕ) (hle : first ≤ second) :
    finiteBudget K variableCount stores bits first≤finiteBudget K variableCount stores bits second := by
  dsimp only [finiteBudget]
  gcongr

/-- `prop:time`, paper/paper.tex: the complete
ordinary multitape formatter clock is explicitly quartic in its
actual raw packet bits, including measured setup and both passes. -/
theorem rawFormatter_budget_le (request : ValidPacket) :
    request.budget≤1000000000000000*(request.val.word.length+1)^4 := by
  have hsource:=formatterSteps_le request.val
    (NearCubicGates.Close.Interfaces.Formats.toks request.formula) request.source request.mode
  have hmono := finiteBudget_mono packetCallee VV MM request.val.word request.steps
    (1000000*(request.val.word.length+1)^2) hsource
  have hTS : TSK packetCallee=3 := rfl
  unfold ValidPacket.budget
  refine hmono.trans ?_
  dsimp only [finiteBudget,finiteInitializeCost,finiteSetupACost,finiteWidth,costB,costC]
  rw [hTS]
  norm_num [VV,MM]
  ring_nf
  omega

end NearQuarticWires.StageFormulaMetadata
