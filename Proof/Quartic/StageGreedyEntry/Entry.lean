import Proof.Quartic.StageGreedyEntry.Ledger
import Proof.Quartic.Program.Pipe

/-!
# The whole actual per-entry chain, from any tuple program and modular input program

Paper: `lem:print`, `lem:residue` and `prop:time`, paper/paper.tex.

`entryChain tuple modIn` composes the stages of `Stages.lean` with `Program.WordFunction.pipe`: retained
width and modulus, the closed formatter, the retained stack width, the tuple call, the equality-row
input, the sealed equality-row constructor, the modular input and the sealed modular reducer. It maps the
literal entry bytes to exactly `entryOutput`. `entryChain_bound` is the selected per-entry clock, given the
selected clock of the tuple program on actual entries and the linear-plus-square clock of the modular
input program.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open StagePrint StageGreedyCollector

variable (B1 B2 : ℕ)

/-- `lem:residue` and `lem:print`, paper/paper.tex: the type of the
modular input stage. -/
abbrev ModularInputStage (mb : GreedyEntry.Request B1 B2→ℕ) :=
  WordFunction (GreedyEntry.Request B1 B2)
    (fun r=>natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++(modularRequest r).stream)))
    (fun r=>frame (modularRequest r).word) mb

/-- `lem:print`, paper/paper.tex: the whole per-entry chain. -/
noncomputable def entryChain {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    {mb : GreedyEntry.Request B1 B2→ℕ} (modIn : ModularInputStage B1 B2 mb) :=
  Program.WordFunction.pipe (Program.WordFunction.pipe (Program.WordFunction.pipe
    (Program.WordFunction.pipe (Program.WordFunction.pipe (Program.WordFunction.pipe
      (Program.WordFunction.pipe (prefixStage B1 B2) (formatStage B1 B2)) (stackStage B1 B2))
      (tupleStage B1 B2 tuple)) (rowsStage B1 B2)) (equalityStage B1 B2)) modIn) (modularStage B1 B2)

/-- `lem:print`, paper/paper.tex: the chain as a per-entry producer. -/
noncomputable def entryProducerOf {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    {mb : GreedyEntry.Request B1 B2→ℕ} (modIn : ModularInputStage B1 B2 mb) : EntryProducer B1 B2 :=
  ⟨_,entryChain B1 B2 tuple modIn⟩

end NearQuarticWires.StageGreedyEntry
