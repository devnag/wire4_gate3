import Proof.Quartic.StageCompiledTerms.PacketTag
import Proof.Quartic.Control.Walks

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.Recovery.HTParts
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: every packet
starts with the true leading marker of its original natural index. -/
theorem packet_word_cons (packet : StageFormulaMetadata.RawWalkPacket) :
    ∃ tail,packet.word=true::tail := by
  have hpos : 1≤natBitLength packet.index := by unfold natBitLength;omega
  have hNat : ∃ tail,RepairRepresentation.natWord packet.index=true::tail := by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_eq]
    generalize natBitLength packet.index=bits at *
    cases bits with
    | zero=>omega
    | succ bits=>exact ⟨_,rfl⟩
  obtain ⟨tail,ht⟩:=hNat
  simp only [StageFormulaMetadata.RawWalkPacket.word,ht,List.cons_append]
  exact ⟨_,rfl⟩

/-- `lem:print`, paper/paper.tex: the batch
stream contains a framed encoded tag and its actual isolated packet. -/
def taggedPacketWords (packets : List StageFormulaMetadata.RawWalkPacket) : List Bool :=
  packets.flatMap fun packet=>frame (packetTag packet)++frame packet.word

/-- `prop:time`, paper/paper.tex: packet tags
add at most a fixed linear factor to the complete literal source. -/
theorem taggedPacketWords_length (packets : List StageFormulaMetadata.RawWalkPacket) :
    (taggedPacketWords packets).length≤
      4*(packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length+2*packets.length := by
  induction packets with
  | nil=>simp [taggedPacketWords]
  | cons packet packets ih=>
    have hp : (packetTag packet).length≤packet.word.length := by
      simp only [packetTag,StageFormulaMetadata.RawWalkPacket.word,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.length_append]
      omega
    simp only [taggedPacketWords,List.flatMap_cons,List.length_append,frame_length,List.length_cons] at *
    omega

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual streaming loop tags and isolates all source
packets in their original order. Each following packet is read only at
its own iteration, and no original source suffix is copied per walk. -/
theorem tagPackets_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC) :
    ∀ (packets : List StageFormulaMetadata.RawWalkPacket) (pre : List Bool) (a : WState ns nr),
      a.st src=pre++packets.flatMap StageFormulaMetadata.RawWalkPacket.word→
      a.sh src=pre.length→a.sh dst=(a.st dst).length→a.val SC=0→a.val K=0→
      a.val OP+20*((packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length+packets.length+1)≤cap→
      WExec cap (.whs src (tagPacket src dst OP SC K)) a
        ((appendO a dst OP (taggedPacketWords packets)).seth src
          (pre.length+(packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length))
        (400*((packets.flatMap StageFormulaMetadata.RawWalkPacket.word).length+packets.length)+1)
  | [],pre,a,hin,hhead,_,_,_,_=>by
      have he : wbit a src=false := by
        simp only [List.flatMap_nil,List.append_nil] at hin
        simp [wbit,readTapeBit,hin,hhead,List.getD_eq_default]
      have hs : ((appendO a dst OP (taggedPacketWords [])).seth src
          (pre.length+([].flatMap StageFormulaMetadata.RawWalkPacket.word).length))=a := by
        simp only [taggedPacketWords,List.flatMap_nil,appendO_nil,List.length_nil,Nat.add_zero]
        rw [←hhead,wseth_same]
      rw [hs]
      simp only [List.flatMap_nil,List.length_nil,Nat.zero_add,Nat.mul_zero]
      exact WExec.whsF he
  | packet::packets,pre,a,hin,hhead,hout,hSC,hK,hcap=>by
      let tail:=packets.flatMap StageFormulaMetadata.RawWalkPacket.word
      have hp : a.st src=pre++packet.word++tail := by
        simpa only [List.flatMap_cons,List.append_assoc] using hin
      obtain ⟨first,hfirst⟩:=packet_word_cons packet
      have hbit : wbit a src=true := by
        simp [wbit,readTapeBit,hp,hhead,hfirst,List.getD_append_right]
      have hcapPacket : a.val OP+6*packet.word.length+10≤cap := by
        simp only [List.flatMap_cons,List.length_append,List.length_cons] at hcap
        omega
      have ePacket:=tagPacket_spec cap src dst OP SC K hsd hOS hKO hKS
        packet pre tail a hp hhead hout hSC hK hcapPacket
      let b:=(appendO a dst OP (frame (packetTag packet)++frame packet.word)).seth src
        (pre.length+packet.word.length)
      have hbsource : b.st src=(pre++packet.word)++tail := by
        simp [b,appendO,Function.update_of_ne hsd,hp,List.append_assoc]
      have hbhead : b.sh src=(pre++packet.word).length := by simp [b,List.length_append]
      have hbout : b.sh dst=(b.st dst).length := by
        simp [b,appendO,Function.update_of_ne hsd.symm,hout,List.length_append]
      have hbSC : b.val SC=0 := by simp [b,appendO,Function.update_of_ne hOS.symm,hSC]
      have hbK : b.val K=0 := by simp [b,appendO,Function.update_of_ne hKO,hK]
      have htag : (packetTag packet).length≤packet.word.length := by
        simp only [packetTag,StageFormulaMetadata.RawWalkPacket.word,List.flatMap_cons,
          List.flatMap_nil,List.append_nil,List.length_append]
        omega
      have hbcap : b.val OP+20*(tail.length+packets.length+1)≤cap := by
        simp only [b,WState.seth_val,appendO_val,Function.update_self,List.length_append,frame_length]
        simp only [List.flatMap_cons,List.length_append,List.length_cons] at hcap
        dsimp only [tail]
        omega
      have eRest:=tagPackets_spec cap src dst OP SC K hsd hOS hKO hKS packets
        (pre++packet.word) b hbsource hbhead hbout hbSC hbK hbcap
      refine (WExec.whsT hbit ePacket eRest).cast cap ?_ ?_
      · apply WState.eq
        · funext stream
          by_cases hi : stream=src
          · subst stream
            simp [b,appendO,hsd,List.length_append]
            omega
          · by_cases ho : stream=dst
            · subst stream
              simp [b,appendO,hsd.symm,taggedPacketWords,List.length_append,frame_length]
              omega
            · simp [b,appendO,Function.update_of_ne hi,Function.update_of_ne ho]
        · funext stream
          by_cases ho : stream=dst
          · subst stream
            simp [b,appendO,taggedPacketWords,List.append_assoc]
          · simp [b,appendO,Function.update_of_ne ho]
        · funext reg
          by_cases ho : reg=OP
          · subst reg
            simp [b,appendO,taggedPacketWords,List.length_append,frame_length]
            omega
          · simp [b,appendO,Function.update_of_ne ho]
        · rfl
      · simp only [List.flatMap_cons,List.length_append,List.length_cons]
        omega

end NearQuarticWires.StageCompiledTerms
