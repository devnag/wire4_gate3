import Proof.Quartic.StageGreedyCollector.FirstEntry
import Proof.Quartic.StageGreedyCollector.PerEntryTarget
import Proof.Quartic.StageGreedyCollector.SourceLength

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open StagePrint

/-- `lem:print`, paper/paper.tex: every
actual selected walk family is nonempty, so its original first index is zero. -/
noncomputable def firstActualEntry {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    GreedyEntry.Request B1 B2 :=⟨r,⟨0,StageLiftSourceCost.walkCount_pos r⟩⟩

theorem actualEntries_nonempty {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    actualEntries r≠[] := by
  intro h
  have hl:=actualEntries_length r
  rw [h] at hl
  have hp:=StageLiftSourceCost.walkCount_pos r
  simp only [List.length_nil] at hl
  omega

theorem actualEntries_first_tail {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    actualEntry (firstActualEntry r)::(actualEntries r).tail=actualEntries r := by
  have h:=List.cons_head_tail (actualEntries_nonempty r)
  rw [show (actualEntries r).head (actualEntries_nonempty r)=actualEntry (firstActualEntry r) by
    unfold actualEntries
    rw [List.head_ofFn]
    rfl] at h
  exact h

/-- `lem:print`, paper/paper.tex: the
first-entry extractor's source is exactly the actual context carrier,
including the entire untouched suffix of subsequent indexed entries. -/
noncomputable def actualFirstRequest {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : FirstRequest :=
  ⟨contextWord r,(actualEntries r).length,actualEntry (firstActualEntry r),
    (actualEntries r).tail.flatMap Entry.word⟩

theorem actualFirstRequest_word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualFirstRequest r).word=contextualWord r := by
  rw [contextualWord_entries]
  have h:=congrArg (List.flatMap Entry.word) (actualEntries_first_tail r)
  simp only [List.flatMap_cons] at h
  simp only [actualFirstRequest,FirstRequest.word]
  rw [List.append_assoc,←h]

theorem actualFirstRequest_output {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (actualFirstRequest r).output=frame (EntryFormat.ofGreedy (firstActualEntry r)).word := by
  exact congrArg frame (contextualEntry_word (firstActualEntry r))

/-- `lem:print`, paper/paper.tex: the
actual first original request is physically extracted from the full
carrier, with no decoded metadata or supplied first-entry assumption. -/
noncomputable def actualFirstWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) contextualWord
      (fun r=>frame (EntryFormat.ofGreedy (firstActualEntry r)).word)
      (fun r=>2*(actualFirstRequest r).steps+2) :=
  ⟨firstEntryWordFunction.program,fun r=>by
    simpa only [actualFirstRequest_word,actualFirstRequest_output] using
      firstEntryWordFunction.realizes (actualFirstRequest r)⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: the header computation receives a real original
entry extracted once, and both physical programs are included in the budget. -/
noncomputable def contextualHeader {B1 B2 : ℕ} (H : HeaderProducer B1 B2) :
    (budget : Greedy.PrintRequest B1 B2→ℕ) ×
      WordFunction (Greedy.PrintRequest B1 B2) contextualWord (fun r=>frame (globalHeader r)) budget :=
  let h : WordFunction (Greedy.PrintRequest B1 B2)
      (fun r=>(EntryFormat.ofGreedy (firstActualEntry r)).word) (fun r=>frame (globalHeader r))
      (fun r=>H.1 (firstActualEntry r)) :=
    ⟨H.2.program,fun r=>H.2.realizes (firstActualEntry r)⟩
  ⟨_,Program.WordFunction.pipe (actualFirstWordFunction B1 B2) h⟩

end NearQuarticWires.StageGreedyCollector
