import Proof.Quartic.StagePrintTuple.SetupContract

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageTuple

/-- `prop:time`, paper/paper.tex: the actual fixed
source loader is exactly linear in the complete source, including Terms;
its finite blank margin is not an arithmetic packet or a public input. -/
theorem sourceLoadCost_linear (r : TermCutRequest) :
    r.sourceLoadCost=6*r.word.length+27 := by
  rw [r.word_sourceFields]
  simp only [TermCutRequest.sourceLoadCost,Top.loadCost,Top.loadChainCost,
    Top.loadRec,List.length_append,frame_length]
  ring

theorem sourceLoadCapacity_linear (r : TermCutRequest) :
    r.sourceLoadCapacity=3*r.word.length+11 := by
  unfold TermCutRequest.sourceLoadCapacity
  rw [r.word_sourceFields]
  simp only [Top.loadChainCost,Top.loadRec,List.length_append,frame_length]
  ring

end NearQuarticWires.StageTupleSetup
