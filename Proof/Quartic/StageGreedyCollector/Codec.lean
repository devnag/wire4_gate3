import Proof.Quartic.StageGreedyCollector.EntryLoop
import Proof.Quartic.StageGreedyCollector.ContextTarget
import Proof.Quartic.StageGreedyCollector.Requests

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open StagePrint

/-- Step 3 and `lem:print`, paper/paper.tex: the actual entry list contains every original low-first
walk ordinal once, including its zero-coefficient case. -/
noncomputable def actualEntries {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Entry :=
  List.ofFn fun i=>actualEntry (⟨r,i⟩ : GreedyEntry.Request B1 B2)

theorem actualEntries_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualEntries r).length=r.child.cellCall.seed.N^8 := by simp [actualEntries]

theorem actualEntries_words {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualEntries r).flatMap Entry.word=(List.ofFn (TermsCarrier.entryWord r)).flatten := by
  simp only [actualEntries,List.flatMap_def,List.map_ofFn,Function.comp_def,actualEntry_word]

theorem contextualWord_entries {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    contextualWord r=frame (contextWord r)++natWord (actualEntries r).length++
      (actualEntries r).flatMap Entry.word := by
  rw [actualEntries_length,actualEntries_words]
  rfl

/-- `lem:print`, paper/paper.tex: the physical
contextual request assembled for one entry is exactly the input of
the shared modular formatter, with no additional runtime parameter. -/
theorem contextualEntry_word {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    contextWord r.source++(actualEntry r).word=(EntryFormat.ofGreedy r).word := by
  rw [actualEntry_word,EntryFormat.ofGreedy_word]
  rfl

/-- `lem:print`, paper/paper.tex: all literal
prepared requests match the real formatter input in original walk order. -/
theorem entryRequests_actual {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    entryRequests (contextWord r) (actualEntries r)=
      (List.ofFn fun i=>frame (EntryFormat.ofGreedy (⟨r,i⟩ : GreedyEntry.Request B1 B2)).word).flatten := by
  simp only [entryRequests,actualEntries,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact congrArg frame (contextualEntry_word (⟨r,i⟩ : GreedyEntry.Request B1 B2))

/-- `lem:print`, paper/paper.tex: one original
star geometry and one proved common weak-field width form the complete
five-natural header of the final native stream. -/
def globalHeader {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  [(GreedyCollector.star r).n,(GreedyCollector.star r).r,(GreedyCollector.star r).b,
    (GreedyCollector.star r).s,GreedyCollector.fieldWidth r].flatMap natWord

theorem collector_word_header {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    GreedyCollector.word r=globalHeader r++GreedyCollector.stream r := rfl

end NearQuarticWires.StageGreedyCollector
