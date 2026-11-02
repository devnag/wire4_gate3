import Proof.Quartic.StageGreedyCollector.StageActual
import Proof.Quartic.StageCompiledTerms.AnswerCopy

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Expand.PolyTab
open StagePrint Reconstruct.Batch StageCompiledTerms Control

/-- `lem:print`, paper/paper.tex: each
real reply contains the literal weak-cut stream after its own equality
split and modular reduction, at the common native field width. -/
noncomputable def entryPayload {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) : List Bool :=
  (GreedyCollector.walkCuts r.source r.index).flatMap
    (MatrixScoreBatch.cutWord (GreedyCollector.fieldWidth r.source))

noncomputable def batchReplies {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  batchOut (globalHeader r) (fun _=>[true]) entryOutput (entryCalls r)

/-- `prop:time`, paper/paper.tex: the
maximum actual call budget bounds the finite reused bank; it is a
proof quantity, not an additional source field or runtime oracle. -/
noncomputable def entryMaximum {B1 B2 : ℕ} (E : EntryProducer B1 B2)
    (r : Greedy.PrintRequest B1 B2) : ℕ :=((entryCalls r).map E.1).foldr max 0

theorem entryMaximum_bound {B1 B2 : ℕ} (E : EntryProducer B1 B2)
    (r : Greedy.PrintRequest B1 B2) (entry : GreedyEntry.Request B1 B2) (he : entry∈entryCalls r) :
    E.1 entry≤entryMaximum E r :=
  List.le_max_of_le (List.mem_map.mpr ⟨entry,he,rfl⟩) le_rfl

noncomputable def entryBatchSteps {B1 B2 : ℕ} (E : EntryProducer B1 B2)
    (r : Greedy.PrintRequest B1 B2) : ℕ :=
  batchCost (globalHeader r) (fun _=>[true]) (fun entry=>(EntryFormat.ofGreedy entry).word)
    entryOutput (entryMaximum E r) (fun entry=>answerCopyCost (entryPayload entry)) (entryCalls r)

noncomputable def entryBatchCapacity {B1 B2 : ℕ} (E : EntryProducer B1 B2)
    (r : Greedy.PrintRequest B1 B2) : ℕ :=
  100*((batchInput r).length+(batchReplies r).length+entryMaximum E r+10)

/-- `lem:print` and `prop:time`, paper/paper.tex: every original request invokes the actual per-entry
ordinary producer on a reused physical bank; its real framed answer
is copied and the bank is erased before the next original request. -/
noncomputable def entryBatchWordFunction {B1 B2 : ℕ} (E : EntryProducer B1 B2) :
    WordFunction (Greedy.PrintRequest B1 B2) batchInput (fun r=>frame (batchReplies r))
      (fun r=>2*entryBatchSteps E r+2) :=
  wordFunction_of_ideal (batchP E.2.program (answerCopier E.2.program)) (cOUT _)
    (by simp [cOUT]) (entryBatchCapacity E) (fun _ _=>0) (entryBatchSteps E) (fun _=>le_rfl) (by
      intro r
      have hb:=entryMaximum_bound E r
      have hcopy : ∀ entry∈entryCalls r,∀ a : WState (cns E.2.program.tapeCount) lnr,
          a.st (cbank _ E.2.program.outputTape)=entryOutput entry→
          a.sh (cbank _ E.2.program.outputTape)=0→a.sh (cT _)=(a.st (cT _)).length→
          (∀ i,a.val (cR i)=0)→
          WExec (entryBatchCapacity E r) (answerCopier E.2.program) a
            (appendT a (cT _) (Streaming.marks (entryOutput entry)))
            (answerCopyCost (entryPayload entry)) := by
        intro entry he a ha hh hout hz
        have hlen:=Control.output_length_le E.2 entry
        have hbud:=hb entry he
        apply answerCopier_spec _ E.2.program _ a ha hh hout hz
        change 2*(entryOutput entry).length+1≤_
        unfold entryBatchCapacity
        omega
      obtain ⟨b,eb,hout⟩:=batchP_exec (entryBatchCapacity E r) E.2 (answerCopier E.2.program)
        (answerCopier_avoids E.2.program) (fun _=>[true])
        (fun entry=>answerCopyCost (entryPayload entry)) (entryMaximum E r)
        (globalHeader r) (entryCalls r) hb hcopy (by
          change 10*((batchInput r).length+(batchReplies r).length+entryMaximum E r+10)≤_
          unfold entryBatchCapacity
          omega)
      exact ⟨rfl,b,eb,hout⟩)

end NearQuarticWires.StageGreedyCollector
