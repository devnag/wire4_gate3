import Proof.Quartic.StageGreedyCollector.EntryBatch

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces (listWord)
open StagePrint Reconstruct.Batch StageCompiledTerms Control

/-- `prop:time`, paper/paper.tex: the
actual batch source pays every input byte once, including the common
header, binary count, reply marker and request frame. -/
theorem batch_input_dominates {R : Type} (header : List Bool) (inp : R→List Bool) (items : List R) :
    header.length+(natWord items.length).length+(items.flatMap inp).length≤
      (frame header++listWord (fun r=>frame [true]++frame (inp r)) items).length := by
  have h : (items.flatMap inp).length≤
      (items.flatMap fun r=>frame [true]++frame (inp r)).length := by
    induction items with
    | nil=>simp
    | cons r rs ih=>simp only [List.flatMap_cons,List.length_append,frame_length] at ih ⊢;omega
  simp only [listWord,List.length_append,frame_length]
  omega

/-- `prop:time`, paper/paper.tex: the
literal item clock charges input copy, one actual bounded call, one
answer copy and cleanup without multiplying two source lengths. -/
theorem batch_items_linear {R : Type} (inp : R→List Bool) (B : ℕ) (cpc : R→ℕ)
    (items : List R) (hc : ∀ r∈items,cpc r≤100*(B+1)+10) :
    itemsCost (fun _=>[true]) inp B cpc items≤
      1000*((items.flatMap inp).length+items.length*(B+1))+1 := by
  induction items with
  | nil=>simp [itemsCost]
  | cons r rs ih=>
      have hr:=hc r (by simp)
      have ht:=ih (fun x hx=>hc x (by simp [hx]))
      have hi : itemCost 1 (inp r).length B (cpc r)+2≤1000*((inp r).length+B+1) := by
        unfold itemCost callCost cleanCost
        omega
      simp only [itemsCost,List.map_cons,List.sum_cons,List.length_singleton] at ht ⊢
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith

/-- `prop:time`, paper/paper.tex: copying
all real bounded replies adds their lengths, with one explicit marker
per original walk; no global row-count square is used. -/
theorem batch_replies_linear {R : Type} (header : List Bool) (out : R→List Bool) (B : ℕ)
    (items : List R) (ho : ∀r∈items,(out r).length≤B+1) :
    (batchOut header (fun _=>[true]) out items).length≤
      header.length+(natWord items.length).length+items.length*(B+2) := by
  have h : (items.flatMap fun r=>[true]++out r).length≤ items.length*(B+2) := by
    induction items with
    | nil=>simp
    | cons r rs ih=>
        have hr:=ho r (by simp)
        have ht:=ih (fun x hx=>ho x (by simp [hx]))
        simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil]
        nlinarith
  simp only [batchOut,listWord,List.length_append]
  omega

/-- `prop:time`, paper/paper.tex: all
actual per-walk output bytes fit the chosen genuine call budget. -/
theorem entry_output_length {B1 B2 : ℕ} (E : EntryProducer B1 B2) (r : Greedy.PrintRequest B1 B2)
    (entry : GreedyEntry.Request B1 B2) (he : entry∈entryCalls r) :
    (entryOutput entry).length≤entryMaximum E r+1 :=
  (output_length_le E.2 entry).trans (Nat.add_le_add_right (entryMaximum_bound E r entry he) 1)

theorem batchReplies_length {B1 B2 : ℕ} (E : EntryProducer B1 B2) (r : Greedy.PrintRequest B1 B2) :
    (batchReplies r).length≤(batchInput r).length+(entryCalls r).length*(entryMaximum E r+2) := by
  have hi:=batch_input_dominates (globalHeader r) (fun e=>(EntryFormat.ofGreedy e).word) (entryCalls r)
  have ho:=batch_replies_linear (globalHeader r) entryOutput (entryMaximum E r) (entryCalls r)
    (entry_output_length E r)
  change (globalHeader r).length+(natWord (entryCalls r).length).length+_≤(batchInput r).length at hi
  change (batchReplies r).length≤_ at ho
  omega

/-- `prop:time`, paper/paper.tex: the
complete real batch clock is linear in its input and walk count times
the actual per-call budget, including all answer copying and cleanup. -/
theorem entryBatchSteps_linear {B1 B2 : ℕ} (E : EntryProducer B1 B2) (r : Greedy.PrintRequest B1 B2) :
    entryBatchSteps E r≤10000*((batchInput r).length+
      (entryCalls r).length*(entryMaximum E r+1)+1) := by
  have hi:=batch_input_dominates (globalHeader r) (fun e=>(EntryFormat.ofGreedy e).word) (entryCalls r)
  have hc:=batch_items_linear (fun e=>(EntryFormat.ofGreedy e).word) (entryMaximum E r)
    (fun e=>answerCopyCost (entryPayload e)) (entryCalls r) (by
      intro e he
      have hh:=entry_output_length E r e he
      unfold answerCopyCost
      change 100*(entryOutput e).length+10≤100*(entryMaximum E r+1)+10
      omega)
  have ho:=batchReplies_length E r
  change (globalHeader r).length+(natWord (entryCalls r).length).length+_≤(batchInput r).length at hi
  unfold entryBatchSteps batchCost
  change (batchOut (globalHeader r) (fun _=>[true]) entryOutput (entryCalls r)).length≤_ at ho
  nlinarith only [hi,hc,ho]

end NearQuarticWires.StageGreedyCollector
