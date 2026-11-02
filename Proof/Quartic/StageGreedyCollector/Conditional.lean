import Proof.Quartic.StageGreedyCollector.FinishActual
import Proof.Quartic.StageGreedyContext.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete ordinary collector computes its context
once, extracts and computes the common header, stages every original
entry, runs each actual weak-row producer, and concatenates the literal
reduced weak bodies. Every physical handoff is included in this same budget. -/
noncomputable def producer_of_header_entry {B1 B2 : ℕ}
    (H : HeaderProducer B1 B2) (E : EntryProducer B1 B2) : GreedyCollector.Producer B1 B2 :=
  let c:=StageGreedyContext.contextProducer B1 B2
  let s:=batchInputProducer_of_header H
  ⟨_,Program.WordFunction.pipe
    (Program.WordFunction.pipe (Program.WordFunction.pipe c.2 s.2) (entryBatchWordFunction E))
    (actualFinishWordFunction B1 B2)⟩

end NearQuarticWires.StageGreedyCollector
