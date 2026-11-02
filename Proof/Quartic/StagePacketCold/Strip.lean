import Proof.Quartic.StagePacketCold.Subtract

set_option autoImplicit false

namespace NearQuarticWires.StagePacketCold

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: one uniform
finite-packet adapter strips a fixed number of actual binary fields
and frames the remaining bytes using their measured size. -/
def stripPrefix (count : ℕ) : WM 2 6 :=
  .seq acquirePacket
    (.seq (StagePacket.copyNaturalFields 1 3 4 (fun _=>.skip) count)
      (.seq (subtractConsumed 3 1)
        (.seq (cntLoop 1 3 1 (fun bit=>emitPair 2 5 bit)) (emitC 2 5 false))))

/-- `prop:time`, paper/paper.tex: the number
of stripped fields is bounded by their actual binary source bytes. -/
theorem fields_count_le_bits (fields : List ℕ) : fields.length≤(fields.flatMap natWord).length := by
  induction fields with
  | nil=>rfl
  | cons value fields ih=>
      simp only [List.length_cons,List.flatMap_cons,List.length_append]
      have hp:=NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length value
      omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the cold adapter physically measures/unframes input,
skips actual field codecs, and copies only its measured remainder.
Every index and hint remains encoded throughout this execution. -/
theorem stripPrefix_run (fields : List ℕ) (tail : List Bool) :
    ∃ last,WXExec (10*((fields.flatMap natWord++tail).length+1))
      (.wm (stripPrefix fields.length)) (packetStart (fields.flatMap natWord++tail)) last
      (300*((fields.flatMap natWord++tail).length+1)) ∧last.st 2=frame tail := by
  let header:=fields.flatMap natWord
  let bits:=header++tail
  let cap:=10*(bits.length+1)
  have hm : bits.length=header.length+tail.length := List.length_append
  have hf : fields.length≤header.length := fields_count_le_bits fields
  have eAcquire:=acquirePacket_spec bits cap (by dsimp [cap];omega)
  let a:=acquiredPacket bits
  have ha1 : a.st 1=header++tail := by simp [a,acquiredPacket,bits]
  have haHead : a.sh 1=0 := by simp [a,acquiredPacket,packetStart,NearCubicGates.Close.Expand.PolyTab.idealStart]
  have haOut : a.sh 2=(a.st 2).length := by
    simp [a,acquiredPacket,packetStart,NearCubicGates.Close.Expand.PolyTab.idealStart]
  have ha4 : a.val 4=0 := by simp [a,acquiredPacket,packetStart,NearCubicGates.Close.Expand.PolyTab.idealStart]
  have ha5 : a.val 5=0 := by simp [a,acquiredPacket,packetStart,NearCubicGates.Close.Expand.PolyTab.idealStart]
  have ha3 : a.val 3=0 := by simp [a,acquiredPacket,packetStart,NearCubicGates.Close.Expand.PolyTab.idealStart]
  have eSkip:=StagePacket.copyNaturalFields_spec cap (1 : Fin 3) 2 (5 : Fin 6) 3 4
    (by decide) (by decide) (by decide) (by decide) (fun _=>.skip) (fun _=>[]) 0 0
    (emits_none (cap:=cap)) (by intro bit;rfl) fields [] tail a
    (by simpa using ha1) haHead haOut ha4 (by rw [ha5];simp)
    (by rw [ha3];change 0+header.length≤cap;dsimp [cap];omega)
  rw [StagePacket.projection_empty_map] at eSkip
  let b:=adv (1 : Fin 3) 2 (5 : Fin 6) 3 a [] header.length
  have hb3 : b.val 3=header.length := by rw [adv_val_SC,ha3,Nat.zero_add]
  have hb1 : b.val 1=bits.length := by
    simp only [b,adv_val_other _ _ _ _ (by decide : (1 : Fin 6)≠5) (by decide : (1 : Fin 6)≠3),a,acquiredPacket,WState.setv_val,
      Function.update_self]
  have eSub:=subtractConsumed_spec cap (3 : Fin 6) 1 (by decide) header.length b hb3
    (by rw [hb1];omega) (by rw [hb1];dsimp [cap];omega)
  let c:=(b.setv 3 0).setv 1 (b.val 1-header.length)
  have hc1 : c.val 1=tail.length := by simp only [c,WState.setv_val,Function.update_self,hb1];omega
  have hc3 : c.val 3=0 := by simp [c]
  have hc5 : c.val 5=0 := by
    simp only [c,WState.setv_val,Function.update_of_ne (by decide : (5 : Fin 6)≠1),
      Function.update_of_ne (by decide : (5 : Fin 6)≠3),b,adv_val_OP (by decide : (5 : Fin 6)≠3),List.length_nil,
      Nat.add_zero,ha5]
  have eTail:=cntLoop_spec (cap:=cap) (src:=(1 : Fin 3)) (dst:=2) (OP:=(5 : Fin 6)) (SC:=3)
    (by decide) (by decide) (K:=1) (by decide) (by decide) (emits_pair (cap:=cap)) [] tail header c
    (by simp only [c,WState.setv_st,b,adv_st_src (by decide : (1 : Fin 3)≠2),ha1,List.append_nil])
    (by simp only [c,WState.setv_sh,b,adv_sh_src,haHead,Nat.zero_add])
    (by simp only [c,WState.setv_sh,WState.setv_st,b,adv_sh_dst (by decide : (1 : Fin 3)≠2),
      adv_st_dst,List.length_nil,List.append_nil,Nat.add_zero];exact haOut)
    hc1 (by dsimp [cap];omega) (by rw [hc5,StagePacket.paired_length];dsimp [cap];omega)
    (by rw [hc3];dsimp [cap];omega)
  let d:=(adv (1 : Fin 3) 2 (5 : Fin 6) 3 c (tail.flatMap fun bit=>[true,bit]) tail.length).setv 1 0
  have hdOut : d.sh 2=(d.st 2).length := by
    simp only [d,WState.setv_sh,WState.setv_st,adv_sh_dst (by decide : (1 : Fin 3)≠2),adv_st_dst,
      c,WState.setv_sh,WState.setv_st,b,
      List.length_nil,List.append_nil,Nat.add_zero,List.length_append]
    rw [haOut]
  have eMark:=NearCubicGates.Close.Codec.emitBit_spec cap (2 : Fin 3) (5 : Fin 6) false d hdOut (by
    simp only [d,WState.setv_val,Function.update_of_ne (by decide : (5 : Fin 6)≠1),
      adv_val_OP (by decide : (5 : Fin 6)≠3),hc5,StagePacket.paired_length]
    dsimp [cap]
    omega)
  let last:=appendO d 2 5 [false]
  refine ⟨last,WXExec.wm ((eAcquire.seq (eSkip.seq (eSub.seq (eTail.seq eMark)))).mono ?_),?_⟩
  · change _≤300*(bits.length+1)
    dsimp only [header] at hm hf ⊢
    omega
  · simp only [last,appendO_st,Function.update_self,d,WState.setv_st,adv_st_dst,c,WState.setv_st,
      b,adv_st_dst,List.append_nil,a,acquiredPacket,WState.setv_st,WState.seth_st,WState.sets_st,
      Function.update_of_ne (by decide : (2 : Fin 3)≠1),packetStart,
      NearCubicGates.Close.Expand.PolyTab.idealStart]
    change []++(tail.flatMap fun bit=>[true,bit])++[false]=frame tail
    simpa only [List.nil_append] using StagePacket.paired_frame tail

end NearQuarticWires.StagePacketCold
