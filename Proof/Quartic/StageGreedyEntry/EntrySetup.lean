import Proof.Quartic.StageGreedyEntry.EntryTuple
import Proof.Quartic.StageTupleSetupCost.Final
import Proof.Quartic.StageTupleSetupCold.Machine

/-!
# The per-entry producer with the actual tuple preparation

Paper: `lem:print` and `prop:time`, paper/paper.tex.

The per-entry chain with the actual cold tuple preparation `StageTupleSetupCold.tupleSetupWordFunction` and
its proved additive clock `StageTupleSetupCost.setupBudget_linear_source`; the only remaining parameter is the
monomial stage machine.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint StageGreedyCollector StageTuple

variable (B1 B2 : ℕ) {B : StageNativeKids.NativeKidsRequest → ℕ}
  {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
    StageNativeKids.NativeKidsRequest.output B} {nativePrice : NativeStagePrice B}

/-- `lem:print`, paper/paper.tex: the per-entry producer with the actual preparation. -/
noncomputable def entryProducerOfMachine (M : TermStageMachine native nativePrice) : EntryProducer B1 B2 :=
  entryProducerOfTuple B1 B2 M StageTupleSetupCold.tupleSetupWordFunction

/-- `prop:time`, paper/paper.tex: its selected per-entry clock. -/
theorem entryProducerOfMachine_bound (M : TermStageMachine native nativePrice) :
    EntryBudgetBound (entryProducerOfMachine B1 B2 M).1 :=
  entryProducerOfTuple_bound B1 B2 M StageTupleSetupCold.tupleSetupWordFunction
    StageTupleSetupCost.setupBudget_linear_source

end NearQuarticWires.StageGreedyEntry
