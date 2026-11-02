import Proof.Quartic.StageGreedyEntry.TupleSharp
import Proof.Quartic.StageGreedyEntry.EntryBound
import Proof.Quartic.StageTupleOuter.Core

/-!
# The per-entry producer with the cold tuple printer

Paper: `lem:print` and `prop:time`, paper/paper.tex.

The whole per-entry chain with the cold tuple printer `StageTupleOuter.termCutWordFunction M setup`, built
from the monomial stage `M` and the tuple preparation `setup`, and its selected per-entry clock from the
preparation clock bound alone (`entryProducerOfTuple_bound`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint StageGreedyCollector StageTuple

variable (B1 B2 : ℕ) {B : StageNativeKids.NativeKidsRequest → ℕ}
  {native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
    StageNativeKids.NativeKidsRequest.output B} {nativePrice : NativeStagePrice B}

/-- `lem:print`, paper/paper.tex: the per-entry producer with the cold tuple printer. -/
noncomputable def entryProducerOfTuple (M : TermStageMachine native nativePrice) {Bs : TermCutRequest → ℕ}
    (setup : WordFunction TermCutRequest TermCutRequest.word (fun r=>frame r.preparedWord) Bs) :
    EntryProducer B1 B2 :=
  entryProducerWith B1 B2 (StageTupleOuter.termCutWordFunction M setup)

/-- `prop:time`, paper/paper.tex: its selected per-entry clock. -/
theorem entryProducerOfTuple_bound (M : TermStageMachine native nativePrice) {Bs : TermCutRequest → ℕ}
    (setup : WordFunction TermCutRequest TermCutRequest.word (fun r=>frame r.preparedWord) Bs)
    (hBs : TupleSetupCost Bs) :
    EntryBudgetBound (entryProducerOfTuple B1 B2 M setup).1 :=
  entryProducerWith_bound B1 B2 _ (tuple_ebb_of_sharp B1 B2 M hBs)

end NearQuarticWires.StageGreedyEntry
