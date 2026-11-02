import Proof.Quartic.StageGreedyEntry.EntrySetup
import Proof.Quartic.StageGreedyEntry.HeaderProducer
import Proof.Quartic.StagePrintTuple.Final

/-!
# The actual per-entry producers

Paper: `lem:print`, `lem:residue` and `prop:time`, paper/paper.tex.

`entryProducer` maps the literal bytes of one actual compiled walk entry to its framed reduced weak cuts at the
common native field width, through the shared formatter, the cold tuple printer with the concrete monomial
stage, the equality-row constructor and the modular reducer. `headerProducer` (`HeaderProducer.lean`) maps the same
bytes to the five common native header scalars. Both clocks meet the selected per-entry bound
`K (n+1)^e (Uocc^(2D)+1)`. No source, row, width, geometry, count or provider premise remains.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open StageGreedyCollector

/-- `lem:print`, paper/paper.tex: the actual per-entry native chain. -/
noncomputable def entryProducer (B1 B2 : ℕ) : EntryProducer B1 B2 :=
  entryProducerOfMachine B1 B2 StageTuple.termStageMachine

/-- `prop:time`, paper/paper.tex: its selected per-entry clock. -/
theorem entryProducer_bound (B1 B2 : ℕ) : EntryBudgetBound (entryProducer B1 B2).1 :=
  entryProducerOfMachine_bound B1 B2 StageTuple.termStageMachine

end NearQuarticWires.StageGreedyEntry
