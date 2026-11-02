import Proof.Quartic.StageGreedyCollector.StagingCost
import Proof.Quartic.StageGreedyCollector.BatchCost

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint

/-- `prop:time`, paper/paper.tex: every
byte of the actual contextual carrier is paid by the complete concrete
once-only context producer, independently of the entry suppliers. -/
theorem contextualWord_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (contextualWord r).length≤(StageGreedyContext.contextProducer B1 B2).1 r := by
  have h:=Control.output_length_le (StageGreedyContext.contextProducer B1 B2).2 r
  rw [frame_length] at h
  omega

/-- `prop:time`, paper/paper.tex: the
SAME complete ordinary collector budget is additive in the actual
context setup and one header call, plus one finite-context copy and
one genuine bounded entry call per original walk. All frames, actual
answer bytes, cleanup and final count removal are included. -/
theorem producerBudget_linear {B1 B2 : ℕ} (H : HeaderProducer B1 B2) (E : EntryProducer B1 B2)
    (r : Greedy.PrintRequest B1 B2) :
    (producer_of_header_entry H E).1 r≤10^15*((StageGreedyContext.contextProducer B1 B2).1 r+
      H.1 (firstActualEntry r)+(entryCalls r).length*((contextWord r).length+entryMaximum E r+2)+1) := by
  have hc:=contextualWord_length r
  have hh:=globalHeader_length H r
  have hs:=actualStaging_budget_linear r
  have hi:=batchInput_length_linear r
  have hp:=batchInputProducer_budget_linear H r
  have hb:=entryBatchSteps_linear E r
  have ho:=batchReplies_length E r
  have hf : 2*(actualReplies r).steps+2=600*((batchReplies r).length+1)+2 := by
    unfold ReplyRequest.steps
    rw [actualReplies_word]
    ring
  change 4*(4*(4*(StageGreedyContext.contextProducer B1 B2).1 r+
      4*(batchInputProducer_of_header H).1 r+12)+4*(2*entryBatchSteps E r+2)+12)+
      4*(2*(actualReplies r).steps+2)+12≤_
  rw [hf]
  nlinarith only [hc,hh,hs,hi,hp,hb,ho]

end NearQuarticWires.StageGreedyCollector
