import Proof.Quartic.StageGreedyCollector.Conditional

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint

/-- `prop:time`, paper/paper.tex: the
one first-entry extraction is linear in the actual contextual carrier;
its finite context and first request are already source substrings. -/
theorem first_steps_linear {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualFirstRequest r).steps≤1200*((contextualWord r).length+1) := by
  have hl:=congrArg List.length (actualFirstRequest_word r)
  simp only [FirstRequest.word,List.length_append,frame_length] at hl
  unfold FirstRequest.steps
  rw [actualFirstRequest_word]
  omega

/-- `prop:time`, paper/paper.tex: all
actual common-header bytes are paid by the real once-only header
producer, with its exact first original request. -/
theorem globalHeader_length {B1 B2 : ℕ} (H : HeaderProducer B1 B2) (r : Greedy.PrintRequest B1 B2) :
    (globalHeader r).length≤H.1 (firstActualEntry r) := by
  have h:=Control.output_length_le H.2 (firstActualEntry r)
  change (frame (globalHeader r)).length≤H.1 (firstActualEntry r)+1 at h
  rw [frame_length] at h
  omega

theorem contextualHeader_budget {B1 B2 : ℕ} (H : HeaderProducer B1 B2) (r : Greedy.PrintRequest B1 B2) :
    (contextualHeader H).1 r≤10000*((contextualWord r).length+H.1 (firstActualEntry r)+1) := by
  have h:=first_steps_linear r
  change 4*(2*(actualFirstRequest r).steps+2)+4*H.1 (firstActualEntry r)+12≤_
  omega

/-- `prop:time`, paper/paper.tex: the
raw staging producer pays every byte of the next batch source, independently
of the later per-entry call costs. -/
theorem actualStaging_budget_linear {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    actualStagingBudget r≤400000*((globalHeader r).length+(contextualWord r).length+
      (entryCalls r).length*((contextWord r).length+1)+1) := by
  let q:=actualStaging r
  have ho:=Control.output_length_le stagingRawWordFunction q
  have hw:=congrArg List.length (actualStaging_word r)
  simp only [List.length_append,frame_length] at hw
  have hn : q.entries.length=(entryCalls r).length := by
    simp [q,actualStaging,actualEntries,entryCalls]
  have hwords : q.batch.words.length=q.entries.length := by simp [StagingRequest.batch]
  have hctx : q.context=contextWord r:=rfl
  have hs : q.steps=400*(q.word.length+q.entries.length*(q.context.length+1)+1):=rfl
  change q.batch.word.length≤2*q.steps+2+1 at ho
  change 2*(2*(2*q.steps+2)+100*(q.batch.word.length+q.batch.words.length+1)+3)+2≤_
  change q.word.length=2*(globalHeader r).length+1+(contextualWord r).length at hw
  simp only [hwords,hs,hn,hctx] at ho ⊢
  nlinarith

theorem batchInput_length_linear {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (batchInput r).length≤actualStagingBudget r := by
  have h:=Control.output_length_le (actualStagingWordFunction B1 B2) r
  rw [frame_length] at h
  omega

/-- `prop:time`, paper/paper.tex: one
physical header call, retained-source copy, original indexed-entry pass
and final batch frame have only additive byte costs. -/
theorem batchInputProducer_budget_linear {B1 B2 : ℕ} (H : HeaderProducer B1 B2)
    (r : Greedy.PrintRequest B1 B2) :
    (batchInputProducer_of_header H).1 r≤10000000*((contextualWord r).length+
      H.1 (firstActualEntry r)+(entryCalls r).length*((contextWord r).length+1)+1) := by
  have hh:=globalHeader_length H r
  have hc:=contextualHeader_budget H r
  have hs:=actualStaging_budget_linear r
  change 4*(2*(2*(contextualHeader H).1 r+
      300*((contextualWord r).length+(globalHeader r).length+1))+2)+
      4*actualStagingBudget r+12≤_
  omega

end NearQuarticWires.StageGreedyCollector
