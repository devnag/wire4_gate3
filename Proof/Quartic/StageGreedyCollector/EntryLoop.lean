import Proof.Quartic.StageGreedyCollector.PrepareEntry

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Reconstruct.Batch (appendT)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: all original
compiled entries receive the same finite context in their original
order, including empty Terms payloads and zero coefficients. -/
def entryRequests (context : List Bool) (entries : List Entry) : List Bool :=
  entries.flatMap fun entry=>frame (context++entry.word)

/-- `lem:print` and `prop:time`, paper/paper.tex: a streaming loop prepares each actual request once;
its clock is linear in all entry bytes plus the repeated finite context. -/
theorem prepareEntries_spec (cap : ℕ) (src cache dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hcd : cache≠dst) (hsc : src≠cache)
    (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC) (context : List Bool) :
    ∀ (entries : List Entry) (pre : List Bool) (a : WState ns nr),
      a.st src=pre++entries.flatMap Entry.word→a.sh src=pre.length→
      a.st cache=frame context→a.sh cache=0→a.sh dst=(a.st dst).length→
      a.val OP=0→a.val SC=0→a.val K=0→
      2*(context.length+(entries.flatMap Entry.word).length)+2≤cap→
      WExec cap (.whs src (prepareEntry src cache dst OP SC K)) a
        ((appendT a dst (entryRequests context entries)).seth src
          (pre.length+(entries.flatMap Entry.word).length))
        (110*(entries.length*(context.length+1)+(entries.flatMap Entry.word).length)+1)
  | [],pre,a,hin,hh,_hcache,_hch,_hout,_hOP,_hSC,_hK,_hc=>by
      have he : wbit a src=false := by
        simp only [List.flatMap_nil,List.append_nil] at hin
        simp [wbit,readTapeBit,hin,hh]
      have hz : ((appendT a dst (entryRequests context [])).seth src
          (pre.length+([].flatMap Entry.word).length))=a := by
        simp only [entryRequests,List.flatMap_nil,appendT,List.append_nil,List.length_nil,Nat.add_zero]
        apply WState.eq
        · funext i
          by_cases hi : i=src
          · subst i;simp [hh]
          · by_cases hd : i=dst
            · subst i;simp [Function.update_of_ne hsd.symm]
            · simp [Function.update_of_ne hi]
        · simp
        · rfl
        · rfl
      rw [hz]
      simp only [List.length_nil,List.flatMap_nil,Nat.zero_mul,Nat.zero_add,Nat.mul_zero]
      exact WExec.whsF he
  | entry::entries,pre,a,hin,hh,hcache,hch,hout,hOP,hSC,hK,hc=>by
      let tail:=entries.flatMap Entry.word
      have hp : a.st src=pre++entry.word++tail := by simpa only [List.flatMap_cons,List.append_assoc] using hin
      obtain ⟨first,hfirst⟩:=entry.word_cons
      have hbit : wbit a src=true := by
        simp [wbit,readTapeBit,hp,hh,hfirst]
      have hcap : 2*(context.length+entry.word.length)+2≤cap := by
        simp only [List.flatMap_cons,List.length_append] at hc
        omega
      have eEntry:=prepareEntry_spec cap src cache dst OP SC K hsd hcd hOS hKO hKS
        context entry pre tail a hp hh hcache hch hout hOP hSC hK hcap
      let b:=(appendT a dst (frame (context++entry.word))).seth src (pre.length+entry.word.length)
      have hbsource : b.st src=(pre++entry.word)++tail := by
        simp [b,appendT,Function.update_of_ne hsd,hp,List.append_assoc]
      have hbhead : b.sh src=(pre++entry.word).length := by simp [b,List.length_append]
      have hbcache : b.st cache=frame context := by simp [b,appendT,Function.update_of_ne hcd,hcache]
      have hbch : b.sh cache=0 := by
        simp [b,appendT,Function.update_of_ne hsc.symm,Function.update_of_ne hcd,hch]
      have hbout : b.sh dst=(b.st dst).length := by
        simp [b,appendT,Function.update_of_ne hsd.symm,hout,List.length_append]
      have hbcap : 2*(context.length+tail.length)+2≤cap := by
        simp only [List.flatMap_cons,List.length_append] at hc
        dsimp only [tail]
        omega
      have eRest:=prepareEntries_spec cap src cache dst OP SC K hsd hcd hsc hOS hKO hKS
        context entries (pre++entry.word) b hbsource hbhead hbcache hbch hbout hOP hSC hK hbcap
      refine (WExec.whsT hbit eEntry eRest).cast cap ?_ ?_
      · apply WState.eq
        · funext i
          by_cases hi : i=src
          · subst i;simp [b,appendT,List.length_append]
            omega
          · by_cases ho : i=dst
            · subst i;simp [b,appendT,hsd.symm,entryRequests,List.length_append]
              omega
            · simp [b,appendT,Function.update_of_ne hi,Function.update_of_ne ho]
        · funext i
          by_cases ho : i=dst
          · subst i;simp [b,appendT,entryRequests,List.append_assoc]
          · simp [b,appendT,Function.update_of_ne ho]
        · rfl
        · rfl
      · simp only [List.length_cons,List.flatMap_cons,List.length_append]
        nlinarith

end NearQuarticWires.StageGreedyCollector
