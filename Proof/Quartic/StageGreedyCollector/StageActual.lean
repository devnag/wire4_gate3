import Proof.Quartic.StageGreedyCollector.FirstActual
import Proof.Quartic.StageGreedyCollector.PrefixCache
import Proof.Quartic.StageGreedyCollector.Staging

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces (listWord)
open StagePrint

/-- `lem:print`, paper/paper.tex: every
original walk index remains a distinct physical call, in the original
low-first order and with its exact zero-weight cases retained. -/
noncomputable def entryCalls {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    List (GreedyEntry.Request B1 B2) :=List.ofFn fun i=>⟨r,i⟩

noncomputable def actualStaging {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : StagingRequest :=
  ⟨globalHeader r,contextWord r,(actualEntries r).length,actualEntries r⟩

theorem actualStaging_word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualStaging r).word=frame (globalHeader r)++contextualWord r := by
  rw [contextualWord_entries]
  simp only [actualStaging,StagingRequest.word,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the
literal source of the real per-entry call loop contains its common
header, the actual binary count and every tagged formatter input. -/
noncomputable def batchInput {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  frame (globalHeader r)++listWord
    (fun entry=>frame [true]++frame (EntryFormat.ofGreedy entry).word) (entryCalls r)

theorem actualStaging_batch {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualStaging r).batch.word=batchInput r := by
  simp only [actualStaging,StagingRequest.batch,BatchSource.word,batchSource,
    batchInput,listWord,entryCalls,actualEntries,requestPairs,List.length_ofFn,
    List.flatMap_def,List.map_ofFn,Function.comp_def,List.append_assoc]
  congr 2
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [contextualEntry_word (⟨r,i⟩ : GreedyEntry.Request B1 B2)]

noncomputable def actualStagingBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  2*frameAfterCost (source:=StagingRequest.batch) (budget:=fun r=>2*r.steps+2) (actualStaging r)+2

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual prepared batch source is emitted by one
ordinary machine, retaining exactly the selected family and common width. -/
noncomputable def actualStagingWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2)
      (fun r=>frame (globalHeader r)++contextualWord r) (fun r=>frame (batchInput r))
      actualStagingBudget :=
  ⟨stagingWordFunction.program,fun r=>by
    simpa only [actualStaging_word,actualStaging_batch,actualStagingBudget] using
      stagingWordFunction.realizes (actualStaging r)⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual first-entry header call precedes the
ordered streaming batch preparation, with all copy and call clocks included. -/
noncomputable def batchInputProducer_of_header {B1 B2 : ℕ} (H : HeaderProducer B1 B2) :
    (budget : Greedy.PrintRequest B1 B2→ℕ) ×
      WordFunction (Greedy.PrintRequest B1 B2) contextualWord (fun r=>frame (batchInput r)) budget :=
  let h:=contextualHeader H
  ⟨_,Program.WordFunction.pipe (prefixWordFunction h.2) (actualStagingWordFunction B1 B2)⟩

end NearQuarticWires.StageGreedyCollector
