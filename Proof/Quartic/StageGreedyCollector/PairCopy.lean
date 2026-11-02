import Proof.Quartic.StageGreedyCollector.TagLoop
import Proof.Quartic.StageGreedyCollector.ReplyStream

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
batch source contains a framed true reply tag and a framed finite
request for every original entry. -/
def requestPairs (words : List (List Bool)) : List Bool :=
  words.flatMap fun word=>frame [true]++frame word

/-- `lem:print`, paper/paper.tex: copy exactly
two actual source frames, preserving every raw bit and measuring
both source and destination advances. -/
def copyRequestPair (src dst : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (frameCopy src SC (fun bit=>emitPair dst OP bit))
    (frameCopy src SC (fun bit=>emitPair dst OP bit))

theorem copyRequestPair_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (word pre rest : List Bool) (a : WState ns nr)
    (hs : a.st src=pre++frame [true]++frame word++rest) (hh : a.sh src=pre.length)
    (hd : a.sh dst=(a.st dst).length)
    (ho : a.val OP+2*(frame [true]++frame word).length≤cap)
    (hc : a.val SC+(frame [true]++frame word).length≤cap) :
    WExec cap (copyRequestPair src dst OP SC) a
      (adv src dst OP SC a ((frame [true]++frame word).flatMap fun bit=>[true,bit])
        (frame [true]++frame word).length) (55*(frame [true]++frame word).length+1) := by
  have e1:=frameCopy_spec cap hsd hOS (emits_pair (cap:=cap))
    (d:=2) (by intro bit;rfl) [true] pre (frame word++rest) a
    (by simpa only [List.append_assoc] using hs) hh hd
    (by simp only [List.length_append] at ho;omega)
    (by simp only [List.length_append] at hc;omega)
  let b:=adv src dst OP SC a ((frame [true]).flatMap fun bit=>[true,bit]) (frame [true]).length
  have hb : b.st src=(pre++frame [true])++frame word++rest := by
    simpa only [b,adv_st_src hsd,List.append_assoc] using hs
  have e2:=frameCopy_spec cap hsd hOS (emits_pair (cap:=cap))
    (d:=2) (by intro bit;rfl) word (pre++frame [true]) rest b hb
    (by rw [adv_sh_src,hh,List.length_append])
    (by rw [adv_sh_dst hsd,adv_st_dst,hd,List.length_append])
    (by rw [adv_val_OP hOS,StagePacket.paired_length];simp only [List.length_append] at ho;omega)
    (by rw [adv_val_SC];simp only [List.length_append] at hc;omega)
  refine (e1.seq e2).cast cap ?_ ?_
  · rw [adv_adv hsd hOS]
    simp only [List.flatMap_append,List.length_append]
  · simp only [List.length_append]
    omega

/-- `lem:print` and `prop:time`, paper/paper.tex: one linear structural pass frames every actual batch
byte without a supplied byte count or numerical walk-index decoder. -/
theorem copyRequestPairs_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) :
    ∀ (words : List (List Bool)) (pre : List Bool) (a : WState ns nr),
      a.st src=pre++requestPairs words→a.sh src=pre.length→a.sh dst=(a.st dst).length→
      a.val OP+2*(requestPairs words).length≤cap→a.val SC+(requestPairs words).length≤cap→
      WExec cap (.whs src (copyRequestPair src dst OP SC)) a
        (adv src dst OP SC a ((requestPairs words).flatMap fun bit=>[true,bit])
          (requestPairs words).length)
        (60*((requestPairs words).length+words.length)+1)
  | [],pre,a,hs,hh,_hd,_ho,_hc=>by
      have hbit : wbit a src=false := by simp [wbit,readTapeBit,hs,hh,requestPairs]
      have he : adv src dst OP SC a ((requestPairs []).flatMap fun bit=>[true,bit])
          (requestPairs []).length=a := by
        apply WState.eq <;> simp [requestPairs,adv,appendO]
      rw [he]
      simp only [requestPairs,List.flatMap_nil,List.length_nil,Nat.add_zero,Nat.mul_zero,Nat.zero_add]
      exact WExec.whsF hbit
  | word::words,pre,a,hs,hh,hd,ho,hc=>by
      let pair:=frame [true]++frame word
      have hlen : (requestPairs (word::words)).length = pair.length+(requestPairs words).length := by
        simp only [requestPairs,List.flatMap_cons,List.length_append,pair]
      rw [hlen] at ho hc
      have hp : a.st src=pre++frame [true]++frame word++requestPairs words := by
        simpa only [requestPairs,List.flatMap_cons,List.append_assoc] using hs
      have hbit : wbit a src=true := by simp [wbit,readTapeBit,hp,hh,frame]
      have ep:=copyRequestPair_spec cap src dst OP SC hsd hOS word pre (requestPairs words) a
        hp hh hd (by change a.val OP+2*pair.length≤cap;omega)
        (by change a.val SC+pair.length≤cap;omega)
      let b:=adv src dst OP SC a (pair.flatMap fun bit=>[true,bit]) pair.length
      have hb : b.st src=(pre++pair)++requestPairs words := by
        simp only [b,adv_st_src hsd,hp,pair,List.append_assoc]
      have er:=copyRequestPairs_spec cap src dst OP SC hsd hOS words (pre++pair) b hb
        (by simp only [b,adv_sh_src,hh,List.length_append,pair])
        (by rw [adv_sh_dst hsd,adv_st_dst,hd,List.length_append])
        (by rw [adv_val_OP hOS,StagePacket.paired_length]
            omega)
        (by rw [adv_val_SC]
            omega)
      refine (WExec.whsT hbit ep er).cast cap ?_ ?_
      · rw [adv_adv hsd hOS]
        simp only [requestPairs,List.flatMap_cons,List.flatMap_append,List.length_append,pair]
      · simp only [requestPairs,List.flatMap_cons,List.length_append,List.length_cons]
        omega

end NearQuarticWires.StageGreedyCollector
