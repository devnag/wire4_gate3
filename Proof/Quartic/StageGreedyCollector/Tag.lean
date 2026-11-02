import Proof.Quartic.StageGreedyCollector.PrepareEntry

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Reconstruct.Batch (appendT)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a true reply
tag is itself framed in the batch source, so an empty answer remains
a genuine entry of the stream. -/
def emitReplyTag (dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (emitC dst OP true) (.seq (emitC dst OP true)
    (.seq (emitC dst OP false) (WM.clear OP)))

theorem emitReplyTag_spec (cap : ℕ) (dst : Fin (ns+1)) (OP : Fin nr)
    (a : WState ns nr) (hd : a.sh dst=(a.st dst).length) (hz : a.val OP=0)
    (hc : 3≤cap) :
    WExec cap (emitReplyTag dst OP) a (appendT a dst (frame [true])) 40 := by
  have e1:=emitC_spec cap dst OP true a hd (by omega)
  let b:=appendO a dst OP [true]
  have e2:=emitC_spec cap dst OP true b (by simp [b,hd]) (by simp [b,hz];omega)
  let c:=appendO b dst OP [true]
  have e3:=emitC_spec cap dst OP false c (by simp [c,b,hd]) (by simp [c,b,hz];omega)
  let d:=appendO c dst OP [false]
  have hv : d.val OP=3 := by simp [d,c,b,hz]
  have e4:=wclear_spec cap OP 3 d hv (by rw [hv];exact hc)
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=dst
    · subst i;simp [d,c,b,appendO,appendT,frame]
    · simp [d,c,b,appendO,appendT,Function.update_of_ne hi]
  · funext i
    by_cases hi : i=dst
    · subst i;simp [d,c,b,appendO,appendT,frame,List.append_assoc]
    · simp [d,c,b,appendO,appendT,Function.update_of_ne hi]
  · funext j
    by_cases hj : j=OP
    · subst j;simp [appendT,hz]
    · simp [d,c,b,appendO,appendT,Function.update_of_ne hj]
  · rfl

/-- `lem:print`, paper/paper.tex: each actual
batch item has the same explicit reply marker and its independently
framed context-plus-entry request. -/
def taggedEntry (src cache dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (emitReplyTag dst OP) (prepareEntry src cache dst OP SC K)

theorem taggedEntry_spec (cap : ℕ) (src cache dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hcd : cache≠dst)
    (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (context : List Bool) (entry : Entry) (pre suffix : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++entry.word++suffix) (hh : a.sh src=pre.length)
    (hcache : a.st cache=frame context) (hch : a.sh cache=0)
    (hout : a.sh dst=(a.st dst).length)
    (hOP : a.val OP=0) (hSC : a.val SC=0) (hK : a.val K=0)
    (hc : 2*(context.length+entry.word.length)+3≤cap) :
    WExec cap (taggedEntry src cache dst OP SC K) a
      ((appendT a dst (frame [true]++frame (context++entry.word))).seth src
        (pre.length+entry.word.length)) (150*(context.length+entry.word.length+1)) := by
  have et:=emitReplyTag_spec cap dst OP a hout hOP (by omega)
  let b:=appendT a dst (frame [true])
  have ep:=prepareEntry_spec cap src cache dst OP SC K hsd hcd hOS hKO hKS
    context entry pre suffix b
    (by simp [b,appendT,Function.update_of_ne hsd,hin])
    (by simp [b,appendT,Function.update_of_ne hsd,hh])
    (by simp [b,appendT,Function.update_of_ne hcd,hcache])
    (by simp [b,appendT,Function.update_of_ne hcd,hch])
    (by simp [b,appendT,hout,List.length_append]) hOP hSC hK (by omega)
  refine (et.seq ep).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst i;simp
    · by_cases ho : i=dst
      · subst i;simp [b,appendT,Function.update_of_ne hsd.symm,List.length_append]
        omega
      · simp [b,appendT,Function.update_of_ne hi,Function.update_of_ne ho]
  · funext i
    by_cases ho : i=dst
    · subst i;simp [b,appendT,List.append_assoc]
    · simp [b,appendT,Function.update_of_ne ho]
  · rfl
  · rfl

end NearQuarticWires.StageGreedyCollector
