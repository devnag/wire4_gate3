import Proof.Quartic.StagePacket.ReadLength

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- Step 3 and `lem:print`, paper/paper.tex: the preparation byte count is decoded once; the
original preparation and actual encoded walk count are copied once. -/
def preparePrefix (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr) : WM ns nr :=
  .seq (StagePacket.readPayloadLength src R)
    (.seq (WM.rewind src (R 2))
      (.seq (StagePacket.copyNaturalFields src (R 2) (R 4) (fun bit=>emitPair dst (R 3) bit) 1)
        (.seq (cntLoop src (R 2) (R 5) (fun bit=>emitPair dst (R 3) bit))
          (.seq (emitC dst (R 3) false)
            (.seq (WM.clear (R 2))
              (.seq (StagePacket.copyNaturalFields src (R 2) (R 4) (fun bit=>emitC dst (R 3) bit) 1)
                (WM.clear (R 2))))))))

/-- `prop:time`, paper/paper.tex: the prefix
clock contains its actual small byte-count decoder and linear copies;
the exponentially many walks are never numerically decoded here. -/
def prefixCost (prep : List Bool) (count : ℕ) : ℕ :=
  StagePacket.payloadLengthCost prep.length+
    100*((natWord prep.length).length+prep.length+(natWord count).length+1)

/-- Step 3 and `prop:time`, paper/paper.tex: the physical one-copy prefix pass leaves every raw
packet unread, copies the original bytes, and resets local counters. -/
theorem preparePrefix_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 16 ↪ Fin nr)
    (hsd : src≠dst) (prep : List Bool) (count : ℕ) (pre suffix : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++natWord prep.length++prep++natWord count++suffix)
    (hhead : a.sh src=pre.length) (hout : a.sh dst=(a.st dst).length)
    (hz : ∀ j : Fin 16,j≠3→a.val (R j)=0)
    (hcap : a.val (R 3)+20*((natWord prep.length).length+prep.length+(natWord count).length+1)+
      2^(natBitLength prep.length+1)≤cap) :
    ∃ b,WExec cap (preparePrefix src dst R) a b (prefixCost prep count) ∧
      b.st src=a.st src ∧
      b.sh src=pre.length+(natWord prep.length++prep++natWord count).length ∧
      b.st dst=a.st dst++frame (natWord prep.length++prep)++natWord count ∧
      b.sh dst=(b.st dst).length ∧
      b.val (R 3)=a.val (R 3)+(frame (natWord prep.length++prep)++natWord count).length ∧
      b.val (R 2)=0 ∧ b.val (R 4)=0 ∧
      b.val (R 13)=a.val (R 13) ∧ b.val (R 14)=a.val (R 14) ∧ b.val (R 15)=a.val (R 15) ∧
      (∀ stream,stream≠src→stream≠dst→b.st stream=a.st stream ∧ b.sh stream=a.sh stream) := by
  have rn {i j : Fin 16} (h : i≠j) : R i≠R j:=R.injective.ne h
  let header:=natWord prep.length
  let tail:=natWord count
  change a.val (R 3)+20*(header.length+prep.length+tail.length+1)+
    2^(natBitLength prep.length+1)≤cap at hcap
  have hlinear : a.val (R 3)+20*(header.length+prep.length+tail.length+1)≤cap :=
    (Nat.le_add_right _ _).trans hcap
  have hsmall : 20*(header.length+prep.length+tail.length+1)≤cap :=
    (Nat.le_add_left _ _).trans hlinear
  have hdecode : 2^(natBitLength prep.length+1)≤cap :=
    (Nat.le_add_left _ _).trans hcap
  clear hcap
  have hlen : prep.length+2≤cap := by
    nlinarith
  have eRead:=StagePacket.readPayloadLength_spec cap src R prep.length pre (prep++tail++suffix) a
    (by simpa only [tail,List.append_assoc] using hin) hhead
    (by intro j hj;apply hz j;simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;omega)
    hdecode hlen (by rw [hz 2 (by decide)];change 0+header.length≤cap;omega)
  let b:=StagePacket.payloadLengthState src R a pre.length prep.length
  have hb2 : b.val (R 2)=header.length := by
    simp [b,StagePacket.payloadLengthState,R.injective.eq_iff,hz,header]
  have eBack:=wrewind_spec cap src (R 2) header.length b hb2 (by omega)
  let c:=(b.setv (R 2) 0).seth src (b.sh src-header.length)
  have hcHead : c.sh src=pre.length := by
    simp [c,b,StagePacket.payloadLengthState,header]
  have hcOut : c.sh dst=(c.st dst).length := by
    simp only [c,WState.seth_sh,Function.update_of_ne hsd.symm,WState.setv_sh,b,
      StagePacket.payloadLengthState,WState.setv_sh,WState.seth_sh,WState.seth_st,WState.setv_st]
    simpa only [Function.update_of_ne hsd.symm] using hout
  have hcK : c.val (R 4)=0 := by
    simp [c,b,StagePacket.payloadLengthState,R.injective.eq_iff,hz]
  have hc2 : c.val (R 2)=0 := by simp [c]
  have hc3 : c.val (R 3)=a.val (R 3) := by
    simp [c,b,StagePacket.payloadLengthState,R.injective.eq_iff]
  have hc5 : c.val (R 5)=prep.length := by
    simp [c,b,StagePacket.payloadLengthState,R.injective.eq_iff]
  have eHead:=StagePacket.copyNaturalFields_spec cap src dst (R 3) (R 2) (R 4)
    hsd (rn (by decide)) (rn (by decide)) (rn (by decide))
    (fun bit=>emitPair dst (R 3) bit) (fun bit=>[true,bit]) 15 2 (emits_pair (cap:=cap))
    (by intro bit;rfl) [prep.length] pre (prep++tail++suffix) c
    (by simpa only [c,WState.seth_st,WState.setv_st,b,StagePacket.payloadLengthState,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,tail] using hin)
    hcHead hcOut hcK (by rw [hc3];simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil];change a.val (R 3)+2*header.length≤cap;omega)
    (by rw [hc2];simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil];change 0+header.length≤cap;omega)
  let d:=adv src dst (R 3) (R 2) c (header.flatMap fun bit=>[true,bit]) header.length
  have eHeadRun : WExec cap
      (StagePacket.copyNaturalFields src (R 2) (R 4) (fun bit=>emitPair dst (R 3) bit) 1)
      c d (28*header.length+1) := by
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_cons,List.length_nil,Nat.reduceAdd] at eHead
    convert eHead using 1
    dsimp only [header]
    ring
  have hd3 : d.val (R 3)=a.val (R 3)+2*header.length := by
    rw [adv_val_OP (rn (by decide)),hc3,StagePacket.paired_length]
  have hd2 : d.val (R 2)=header.length := by rw [adv_val_SC,hc2,Nat.zero_add]
  have hd5 : d.val (R 5)=prep.length := by rw [adv_val_other _ _ _ _ (rn (by decide)) (rn (by decide)),hc5]
  have hdOut : d.sh dst=(d.st dst).length := by rw [adv_sh_dst hsd,adv_st_dst,hcOut,List.length_append]
  have ePrep:=cntLoop_spec (cap:=cap) (src:=src) (dst:=dst) (OP:=R 3) (SC:=R 2)
    hsd (rn (by decide)) (K:=R 5) (rn (by decide)) (rn (by decide))
    (emits_pair (cap:=cap)) (tail++suffix) prep (pre++header) d
    (by simp only [d,adv_st_src hsd,c,WState.seth_st,WState.setv_st,b,
      StagePacket.payloadLengthState,hin,header,tail,List.append_assoc])
    (by rw [adv_sh_src,hcHead,List.length_append]) hdOut hd5 (by omega)
    (by rw [hd3,StagePacket.paired_length];omega) (by rw [hd2];omega)
  let e:=(adv src dst (R 3) (R 2) d (prep.flatMap fun bit=>[true,bit]) prep.length).setv (R 5) 0
  have he2 : e.val (R 2)=header.length+prep.length := by
    simp only [e,WState.setv_val,Function.update_of_ne (rn (by decide : (2:Fin 16)≠5)),adv_val_SC,hd2]
  have he3 : e.val (R 3)=a.val (R 3)+2*header.length+2*prep.length := by
    simp only [e,WState.setv_val,Function.update_of_ne (rn (by decide : (3:Fin 16)≠5)),
      adv_val_OP (rn (by decide : (3:Fin 16)≠2)),hd3,StagePacket.paired_length]
  have heOut : e.sh dst=(e.st dst).length := by
    simp only [e,WState.setv_sh,WState.setv_st,adv_sh_dst hsd,adv_st_dst,hdOut,List.length_append]
  have eEnd:=NearCubicGates.Close.Codec.emitBit_spec cap dst (R 3) false e heOut (by rw [he3];omega)
  let f:=appendO e dst (R 3) [false]
  have hf2 : f.val (R 2)=header.length+prep.length := by
    simp only [f,appendO_val,Function.update_of_ne (rn (by decide : (2:Fin 16)≠3)),he2]
  have eClear:=wclear_spec cap (R 2) (header.length+prep.length) f hf2 (by omega)
  let g:=f.setv (R 2) 0
  have hg3 : g.val (R 3)=a.val (R 3)+2*header.length+2*prep.length+1 := by
    simp only [g,WState.setv_val,Function.update_of_ne (rn (by decide : (3:Fin 16)≠2)),f,
      appendO_val,Function.update_self,he3,List.length_singleton]
  have hg2 : g.val (R 2)=0 := by simp [g]
  have hg4 : g.val (R 4)=0 := by
    simp [g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,R.injective.eq_iff,hz]
  have hgOut : g.sh dst=(g.st dst).length := by
    simp only [g,WState.setv_sh,WState.setv_st,f,appendO_sh,appendO_st,Function.update_self,
      heOut,List.length_append,List.length_singleton]
  have hgSource : g.st src=(pre++header++prep)++tail++suffix := by
    simp [g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,hsd,hin,header,tail,List.append_assoc]
  have hgHead : g.sh src=(pre++header++prep).length := by
    simp only [g,WState.setv_sh,f,appendO_sh,Function.update_of_ne hsd,e,WState.setv_sh,
      adv_sh_src,d,adv_sh_src,hcHead,List.length_append]
  have eCount:=StagePacket.copyNaturalFields_spec cap src dst (R 3) (R 2) (R 4)
    hsd (rn (by decide)) (rn (by decide)) (rn (by decide))
    (fun bit=>emitC dst (R 3) bit) (fun bit=>[bit]) 7 1 (emits_raw (cap:=cap))
    (by intro bit;rfl) [count] (pre++header++prep) suffix g
    (by simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using hgSource)
    hgHead hgOut hg4 (by rw [hg3];simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil];change _+1*tail.length≤cap;omega)
    (by rw [hg2];simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil];change 0+tail.length≤cap;omega)
  let h:=adv src dst (R 3) (R 2) g tail tail.length
  have hsingle : (natWord count).flatMap (fun bit=>[bit])=natWord count := by
    generalize natWord count=bits
    induction bits with
    | nil=>rfl
    | cons bit bits ih=>simp only [List.flatMap_cons,ih,List.singleton_append]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.flatMap_id] at eCount
  have eCountRun : WExec cap
      (StagePacket.copyNaturalFields src (R 2) (R 4) (fun bit=>emitC dst (R 3) bit) 1)
      g h (20*tail.length+1) := by
    simp only [List.length_cons,List.length_nil,Nat.reduceAdd,List.flatMap_cons,List.flatMap_nil,List.append_nil] at eCount
    convert eCount using 1
    · simp only [h,hsingle]
      rfl
    · dsimp only [tail]
      ring
  have hh2 : h.val (R 2)=tail.length := by rw [adv_val_SC,hg2,Nat.zero_add]
  have eClearLast:=wclear_spec cap (R 2) tail.length h hh2 (by omega)
  let last:=h.setv (R 2) 0
  refine ⟨last,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (eRead.seq (eBack.seq (eHeadRun.seq (ePrep.seq (eEnd.seq (eClear.seq
      (eCountRun.seq eClearLast))))))).mono (by unfold prefixCost;change _≤_+100*(header.length+prep.length+tail.length+1);omega)
  · simp [last,h,g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,hsd]
  · simp only [last,WState.setv_sh,h,adv_sh_src,hgHead,List.length_append]
    simp only [header,tail,Nat.add_assoc]
  · simp only [last,WState.setv_st,h,adv_st_dst,g,WState.setv_st,f,appendO_st,
      Function.update_self,e,WState.setv_st,adv_st_dst,d,adv_st_dst,c,WState.seth_st,
      WState.setv_st,b,StagePacket.payloadLengthState,WState.setv_st,WState.seth_st]
    rw [←StagePacket.paired_frame (natWord prep.length++prep)]
    simp only [List.flatMap_append,header,tail,List.append_assoc]
  · simp only [last,WState.setv_sh,WState.setv_st,h,adv_sh_dst hsd,adv_st_dst,
      hgOut,List.length_append]
  · simp only [last,WState.setv_val,Function.update_of_ne (rn (by decide : (3:Fin 16)≠2)),
      h,adv_val_OP (rn (by decide : (3:Fin 16)≠2)),hg3,frame_length,List.length_append]
    dsimp only [header,tail] at *
    omega
  · simp [last]
  · simp [last,h,g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,R.injective.eq_iff,hz]
  · simp [last,h,g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,R.injective.eq_iff]
  · simp [last,h,g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,R.injective.eq_iff]
  · simp [last,h,g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,R.injective.eq_iff]
  · intro stream hs ht
    constructor <;> simp [last,h,g,f,e,d,adv,appendO,c,b,StagePacket.payloadLengthState,
      Function.update_of_ne hs,Function.update_of_ne ht]

end NearQuarticWires.StageCompiledTerms
