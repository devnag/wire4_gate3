import Proof.Quartic.StageGreedyCollector.PairCopy

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a common
header, one encoded count, and the actual ordered framed requests. -/
def batchSource (header : List Bool) (count : ℕ) (words : List (List Bool)) : List Bool :=
  frame header++natWord count++requestPairs words

/-- `lem:print`, paper/paper.tex: the structural
framing pass reads the actual header and binary count and then every tagged
request, without a numerical decode of the count or indices. -/
def frameBatch (src dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (frameCopy src SC (fun bit=>emitPair dst OP bit))
    (.seq (StagePacket.copyNaturalFields src SC K (fun bit=>emitPair dst OP bit) 1)
      (.seq (.whs src (copyRequestPair src dst OP SC)) (emitC dst OP false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: every real batch byte is framed by a linear physical pass;
the count is copied as bits and all empty request bodies are retained. -/
theorem frameBatch_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (header : List Bool) (count : ℕ) (words : List (List Bool)) (pre : List Bool)
    (a : WState ns nr) (hs : a.st src=pre++batchSource header count words)
    (hh : a.sh src=pre.length) (hd : a.sh dst=(a.st dst).length) (hK : a.val K=0)
    (ho : a.val OP+2*(batchSource header count words).length+1≤cap)
    (hc : a.val SC+(batchSource header count words).length≤cap) :
    WExec cap (frameBatch src dst OP SC K) a
      (appendO (adv src dst OP SC a
        ((batchSource header count words).flatMap fun bit=>[true,bit])
        (batchSource header count words).length) dst OP [false])
      (100*((batchSource header count words).length+words.length+1)) := by
  have hs0 : a.st src=pre++frame header++(natWord count++requestPairs words) := by
    simpa only [batchSource,List.append_assoc] using hs
  have e1:=frameCopy_spec cap hsd hOS (emits_pair (cap:=cap))
    (d:=2) (by intro bit;rfl) header pre (natWord count++requestPairs words) a hs0 hh hd
    (by simp only [batchSource,List.length_append] at ho;omega)
    (by simp only [batchSource,List.length_append] at hc;omega)
  let b:=adv src dst OP SC a ((frame header).flatMap fun bit=>[true,bit]) (frame header).length
  have hs1 : b.st src=(pre++frame header)++[count].flatMap natWord++requestPairs words := by
    simp only [b,adv_st_src hsd,hs0,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  have e2:=StagePacket.copyNaturalFields_spec cap src dst OP SC K hsd hOS hKO hKS
    (fun bit=>emitPair dst OP bit) (fun bit=>[true,bit]) 15 2
    (emits_pair (cap:=cap)) (by intro bit;rfl) [count] (pre++frame header) (requestPairs words) b hs1
    (by rw [adv_sh_src,hh,List.length_append])
    (by rw [adv_sh_dst hsd,adv_st_dst,hd,List.length_append])
    (by rw [adv_val_other _ _ _ K hKO hKS,hK])
    (by rw [adv_val_OP hOS,StagePacket.paired_length]
        simp only [batchSource,List.length_append] at ho
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil];omega)
    (by rw [adv_val_SC]
        simp only [batchSource,List.length_append] at hc
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil];omega)
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_singleton] at e2
  let c:=adv src dst OP SC b ((natWord count).flatMap fun bit=>[true,bit]) (natWord count).length
  have hs2 : c.st src=(pre++frame header++natWord count)++requestPairs words := by
    simp only [c,b,adv_st_src hsd,hs0,List.append_assoc]
  have e3:=copyRequestPairs_spec cap src dst OP SC hsd hOS words
    (pre++frame header++natWord count) c hs2
    (by rw [adv_sh_src,adv_sh_src,hh];simp only [List.length_append])
    (by rw [adv_sh_dst hsd,adv_st_dst,adv_sh_dst hsd,adv_st_dst,hd,List.length_append,List.length_append])
    (by rw [adv_val_OP hOS,adv_val_OP hOS,StagePacket.paired_length,StagePacket.paired_length]
        simp only [batchSource,List.length_append] at ho;omega)
    (by rw [adv_val_SC,adv_val_SC];simp only [batchSource,List.length_append] at hc;omega)
  let d:=adv src dst OP SC c ((requestPairs words).flatMap fun bit=>[true,bit]) (requestPairs words).length
  have hd' : d.sh dst=(d.st dst).length := by
    rw [adv_sh_dst hsd,adv_st_dst,adv_sh_dst hsd,adv_st_dst,adv_sh_dst hsd,adv_st_dst,hd]
    simp only [List.length_append]
  have hv : d.val OP<cap := by
    rw [adv_val_OP hOS,adv_val_OP hOS,adv_val_OP hOS]
    simp only [StagePacket.paired_length,batchSource,List.length_append] at ho ⊢
    omega
  have e4:=emitC_spec cap dst OP false d hd' hv
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ ?_
  · change appendO d dst OP [false]=_
    dsimp only [d,c,b]
    rw [adv_adv hsd hOS,adv_adv hsd hOS]
    simp only [batchSource,List.flatMap_append,List.length_append,List.append_assoc]
  · simp only [batchSource,List.length_append]
    omega

end NearQuarticWires.StageGreedyCollector
