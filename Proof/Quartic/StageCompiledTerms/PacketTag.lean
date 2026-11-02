import Proof.Quartic.StagePacket.Isolation

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
source index, degree and modulus remain encoded in the entry tag. -/
def packetTag (packet : StageFormulaMetadata.RawWalkPacket) : List Bool :=
  [packet.index,packet.degree,packet.modulus].flatMap natWord

/-- `lem:print`, paper/paper.tex: copy the tag,
return across its measured bytes, isolate this one raw packet and
clear only its local measured counter before the next walk. -/
def tagPacket (src dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (StagePacket.copyNaturalFields src SC K (fun bit=>emitPair dst OP bit) 3)
    (.seq (emitC dst OP false)
      (.seq (WM.rewind src SC)
        (.seq (StagePacket.copyPacketBody src dst OP SC K)
          (.seq (emitC dst OP false) (WM.clear SC)))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the physical tag/isolation pass reads no following
packet and never decodes an index to a unary magnitude. The source
head advances by exactly this packet's real serialized byte count. -/
theorem tagPacket_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (packet : StageFormulaMetadata.RawWalkPacket) (pre suffix : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++packet.word++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (hSC : a.val SC=0) (hK : a.val K=0)
    (hcap : a.val OP+6*packet.word.length+10≤cap) :
    WExec cap (tagPacket src dst OP SC K) a
      ((appendO a dst OP (frame (packetTag packet)++frame packet.word)).seth src
        (pre.length+packet.word.length)) (300*(packet.word.length+1)) := by
  let tag:=packetTag packet
  let rest:=natWord packet.arity++frame packet.payload
  have hp : packet.word=tag++rest := by
    simp only [StageFormulaMetadata.RawWalkPacket.word,packetTag,tag,rest,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  have hlen : tag.length≤packet.word.length := by rw [hp,List.length_append];omega
  have eTag:=StagePacket.copyNaturalFields_spec cap src dst OP SC K hsd hOS hKO hKS
    (fun bit=>emitPair dst OP bit) (fun bit=>[true,bit]) 15 2 (emits_pair (cap:=cap))
    (by intro bit;rfl) [packet.index,packet.degree,packet.modulus] pre (rest++suffix) a
    (by change a.st src=pre++tag++(rest++suffix)
        simpa only [hp,List.append_assoc] using hin) hhead hout hK
    (by change a.val OP+2*tag.length≤cap;omega)
    (by rw [hSC];change 0+tag.length≤cap;omega)
  let b:=adv src dst OP SC a (tag.flatMap fun bit=>[true,bit]) tag.length
  have eTagRun : WExec cap
      (StagePacket.copyNaturalFields src SC K (fun bit=>emitPair dst OP bit) 3) a b
      (28*tag.length+3) := by
    convert eTag using 1 <;> try rfl
    dsimp only [tag,packetTag]
    simp only [List.length_cons,List.length_nil]
    ring
  have hbSC : b.val SC=tag.length := by rw [adv_val_SC,hSC,Nat.zero_add]
  have hbOP : b.val OP=a.val OP+2*tag.length := by
    rw [adv_val_OP hOS,StagePacket.paired_length]
  have hbout : b.sh dst=(b.st dst).length := by
    rw [adv_sh_dst hsd,adv_st_dst,hout,List.length_append]
  have eTagEnd:=NearCubicGates.Close.Codec.emitBit_spec cap dst OP false b hbout
    (by rw [hbOP];omega)
  let c:=appendO b dst OP [false]
  have hcSC : c.val SC=tag.length := by
    simp only [c,appendO_val,Function.update_of_ne hOS.symm,hbSC]
  have eBack:=wrewind_spec cap src SC tag.length c hcSC (by omega)
  let d:=(c.setv SC 0).seth src (c.sh src-tag.length)
  have hdHead : d.sh src=pre.length := by
    simp only [d,WState.seth_sh,Function.update_self,WState.setv_sh,c,appendO_sh,
      Function.update_of_ne hsd,b,adv_sh_src,hhead]
    omega
  have hdSC : d.val SC=0 := by simp [d]
  have hdK : d.val K=0 := by
    simp only [d,WState.seth_val,WState.setv_val,Function.update_of_ne hKS,
      c,appendO_val,Function.update_of_ne hKO,b,adv_val_other _ _ _ K hKO hKS,hK]
  have hdOut : d.sh dst=(d.st dst).length := by
    simp only [d,WState.seth_sh,Function.update_of_ne hsd.symm,WState.setv_sh,
      WState.seth_st,WState.setv_st,c,appendO_sh,appendO_st,Function.update_self,
      List.length_append,List.length_singleton]
    omega
  have hdOP : d.val OP=a.val OP+2*tag.length+1 := by
    simp only [d,WState.seth_val,WState.setv_val,Function.update_of_ne hOS,
      c,appendO_val,Function.update_self,hbOP,List.length_singleton]
  have ePacket:=StagePacket.copyPacketBody_spec cap src dst OP SC K hsd hOS hKO hKS
    packet pre suffix d
    (by simp only [d,WState.seth_st,WState.setv_st,c,appendO_st,Function.update_of_ne hsd,
      b,adv_st_src hsd,hin]) hdHead hdOut hdK (by rw [hdOP];omega)
    (by rw [hdSC];omega)
  let e:=adv src dst OP SC d (packet.word.flatMap fun bit=>[true,bit]) packet.word.length
  have heSC : e.val SC=packet.word.length := by rw [adv_val_SC,hdSC,Nat.zero_add]
  have heOP : e.val OP=a.val OP+2*tag.length+1+2*packet.word.length := by
    rw [adv_val_OP hOS,hdOP,StagePacket.paired_length]
  have heOut : e.sh dst=(e.st dst).length := by
    rw [adv_sh_dst hsd,adv_st_dst,hdOut,List.length_append]
  have eEnd:=NearCubicGates.Close.Codec.emitBit_spec cap dst OP false e heOut
    (by rw [heOP];omega)
  let f:=appendO e dst OP [false]
  have hfSC : f.val SC=packet.word.length := by
    simp only [f,appendO_val,Function.update_of_ne hOS.symm,heSC]
  have eClear:=wclear_spec cap SC packet.word.length f hfSC (by omega)
  refine (eTagRun.seq (eTagEnd.seq (eBack.seq (ePacket.seq (eEnd.seq eClear))))).cast cap ?_ ?_
  · apply WState.eq
    · funext stream
      by_cases hs : stream=src
      · subst stream
        simp only [WState.setv_sh,f,appendO_sh,Function.update_of_ne hsd,
          e,adv_sh_src,hdHead,WState.seth_sh,Function.update_self]
      · by_cases ht : stream=dst
        · subst stream
          simp only [WState.setv_sh,f,appendO_sh,Function.update_self,e,adv_sh_dst hsd,
            d,WState.seth_sh,Function.update_of_ne hsd.symm,WState.setv_sh,c,appendO_sh,
            b,adv_sh_dst hsd,StagePacket.paired_length,List.length_singleton,
            WState.seth_sh,Function.update_of_ne hsd.symm,frame_length,List.length_append]
          dsimp only [tag] at *
          omega
        · simp only [WState.setv_sh,f,appendO_sh,Function.update_of_ne ht,e,
            adv_sh_other _ _ _ _ ht hs,d,WState.seth_sh,Function.update_of_ne hs,
            WState.setv_sh,c,appendO_sh,b,adv_sh_other _ _ _ _ ht hs]
    · funext stream
      by_cases ht : stream=dst
      · subst stream
        simp only [WState.setv_st,f,appendO_st,Function.update_self,e,adv_st_dst,d,
          WState.seth_st,WState.setv_st,c,appendO_st,b,adv_st_dst,List.append_assoc]
        rw [←StagePacket.paired_frame tag,←StagePacket.paired_frame packet.word]
        simp only [List.append_assoc]
      · simp only [WState.setv_st,f,appendO_st,Function.update_of_ne ht,e,
          adv_st_other _ _ _ _ ht,d,WState.seth_st,WState.setv_st,c,appendO_st,b,
          adv_st_other _ _ _ _ ht]
    · funext reg
      by_cases hr : reg=SC
      · subst reg
        simp only [WState.setv_val,Function.update_self,WState.seth_val,appendO_val,
          Function.update_of_ne hOS.symm,hSC]
      · by_cases ho : reg=OP
        · subst reg
          simp only [WState.setv_val,Function.update_of_ne hOS,WState.seth_val,appendO_val,
            Function.update_self,f,heOP,List.length_singleton,frame_length,List.length_append]
          dsimp only [tag] at *
          omega
        · simp only [WState.setv_val,Function.update_of_ne hr,WState.seth_val,appendO_val,
            Function.update_of_ne ho,f,e,adv_val_other _ _ _ reg ho hr,d,
            WState.setv_val,Function.update_of_ne hr,c,b,adv_val_other _ _ _ reg ho hr]
    · rfl
  · have hword : packet.word.length=(packet.header.flatMap natWord).length+(frame packet.payload).length := by
      rw [packet.word_header,List.length_append]
    change _≤300*(packet.word.length+1)
    simp only [List.length_cons,List.length_nil] at *
    omega

end NearQuarticWires.StageCompiledTerms
