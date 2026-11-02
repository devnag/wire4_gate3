import Proof.Quartic.StageGreedyCollector.Finish
import Proof.Quartic.StageGreedyCollector.EntryBatch

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces (listWord)
open StagePrint Reconstruct.Batch

/-- `lem:print`, paper/paper.tex: the
single final reply source uses the original common star header and
all actual per-walk weak-cut replies, including empty and zero cases. -/
noncomputable def actualReplies {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ReplyRequest where
  fields:=![(GreedyCollector.star r).n,(GreedyCollector.star r).r,
    (GreedyCollector.star r).b,(GreedyCollector.star r).s,GreedyCollector.fieldWidth r]
  count:=(entryCalls r).length
  replies:=(entryCalls r).map entryPayload

theorem actualReplies_header {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualReplies r).header=globalHeader r := by
  simp [actualReplies,ReplyRequest.header,globalHeader,List.ofFn_succ]

theorem actualReplies_word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualReplies r).word=batchReplies r := by
  rw [ReplyRequest.word,actualReplies_header]
  simp only [actualReplies,batchReplies,batchOut,listWord,replyWord,List.flatMap_map,
    entryOutput,entryPayload,List.singleton_append,List.append_assoc]

theorem actualReplies_output {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualReplies r).output=frame (GreedyCollector.word r) := by
  rw [ReplyRequest.output,actualReplies_header,collector_word_header]
  congr 2
  simp only [actualReplies,entryCalls,List.map_ofFn,Function.comp_def,entryPayload,
    GreedyCollector.stream]

/-- `lem:print` and `prop:time`, paper/paper.tex: the final actual concatenation copies the header
once, skips the encoded count physically and emits exactly the frozen
native weak-row source, without a global equality square. -/
noncomputable def actualFinishWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) batchReplies (fun r=>frame (GreedyCollector.word r))
      (fun r=>2*(actualReplies r).steps+2) :=
  ⟨finishWordFunction.program,fun r=>by
    simpa only [actualReplies_word,actualReplies_output] using
      finishWordFunction.realizes (actualReplies r)⟩

end NearQuarticWires.StageGreedyCollector
