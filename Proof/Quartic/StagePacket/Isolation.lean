import Proof.Quartic.StagePacket.PacketBody

set_option autoImplicit false

namespace NearQuarticWires.StagePacket

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open StagePrint.PacketInterface

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
packet reader copies its finite prefix, seals the child input frame,
and updates the global cursor from its measured local byte count. -/
def isolatePacket (src dst : Fin (ns+1)) (OP SC LEN K TMP : Fin nr) : WM ns nr :=
  .seq (copyPacketBody src dst OP LEN K)
    (.seq (emitC dst OP false) (addTo LEN SC TMP))

/-- `lem:print`, paper/paper.tex: paired copied
bits followed by their terminal marker are exactly the ordinary frame. -/
theorem paired_frame (bits : List Bool) :
    (bits.flatMap fun bit=>[true,bit])++[false]=frame bits := by
  induction bits with
  | nil=>rfl
  | cons bit bits ih=>
      simpa only [List.flatMap_cons,List.cons_append,List.nil_append,frame] using
        (congrArg (fun rest=>true::bit::rest) ih)

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact actual prefix-isolation contract is realized
with a measured length and a linear clock independent of unread bytes. -/
theorem isolatePacket_spec : IsolationSpec (@isolatePacket ns nr) := by
  intro cap src dst OP SC LEN K TMP hsd hregs packet pre suffix a
    hsource hhead hd hdh hOP hSC hLEN hK hTMP hcap
  have hne (i j : Fin 5) (hij : i≠j) :
      ([OP,SC,LEN,K,TMP] : List (Fin nr)).get i≠([OP,SC,LEN,K,TMP] : List (Fin nr)).get j :=
    hregs.injective_get.ne hij
  have hOL : OP≠LEN := hne 0 2 (by decide)
  have hKO : K≠OP := hne 3 0 (by decide)
  have hKL : K≠LEN := hne 3 2 (by decide)
  have hSL : SC≠LEN := hne 1 2 (by decide)
  have hSO : SC≠OP := hne 1 0 (by decide)
  have hKS : K≠SC := hne 3 1 (by decide)
  have hTO : TMP≠OP := hne 4 0 (by decide)
  have hTL : TMP≠LEN := hne 4 2 (by decide)
  have hTS : TMP≠SC := hne 4 1 (by decide)
  have hLS : LEN≠SC := hSL.symm
  have hLT : LEN≠TMP := hTL.symm
  have hST : SC≠TMP := hTS.symm
  have eBody:=copyPacketBody_spec cap src dst OP LEN K hsd hOL hKO hKL packet pre suffix a
    hsource hhead (by rw [hd,hdh];rfl) hK (by rw [hOP];omega) (by rw [hLEN];omega)
  let b:=adv src dst OP LEN a (packet.word.flatMap fun bit=>[true,bit]) packet.word.length
  have hpairlen : (packet.word.flatMap fun bit=>[true,bit]).length=2*packet.word.length :=
    paired_length packet.word
  have hbout : b.sh dst=(b.st dst).length := by
    rw [adv_sh_dst hsd,adv_st_dst,hd,hdh]
    simp
  have eMark:=NearCubicGates.Close.Codec.emitBit_spec cap dst OP false b hbout (by
    rw [adv_val_OP hOL,hOP,hpairlen]
    omega)
  let c:=appendO b dst OP [false]
  have hcL : c.val LEN=packet.word.length := by
    simp only [c,b,appendO_val,Function.update_of_ne hOL.symm,adv_val_SC,hLEN,Nat.zero_add]
  have hcSC : c.val SC=pre.length := by
    simp only [c,b,appendO_val,Function.update_of_ne hSO,adv_val_other _ _ _ SC hSO hSL,hSC]
  have hcTMP : c.val TMP=0 := by
    simp only [c,b,appendO_val,Function.update_of_ne hTO,adv_val_other _ _ _ TMP hTO hTL,hTMP]
  have eGlobal:=addTo_spec cap LEN SC TMP hLS hLT hST c hcTMP (by rw [hcL];omega)
    (by rw [hcSC,hcL];rw [hSC] at hcap;omega)
  let last:=c.setv SC (c.val SC+c.val LEN)
  have hlen : packet.word.length=
      (packet.header.flatMap NearCubicWires.RepairRepresentation.natWord).length+(frame packet.payload).length := by
    rw [packet.word_header,List.length_append]
  have eRun : WExec cap (isolatePacket src dst OP SC LEN K TMP) a last
      (100*(packet.word.length+1)) := by
    refine (WExec.seq eBody (WExec.seq eMark eGlobal)).mono ?_
    rw [hcL]
    rw [hlen]
    omega
  refine ⟨last,eRun,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  · simp only [last,WState.setv_st,c,b,appendO_st,Function.update_of_ne hsd,adv_st_src hsd]
  · simp only [last,WState.setv_sh,c,b,appendO_sh,Function.update_of_ne hsd,adv_sh_src,hhead]
  · simp only [last,WState.setv_st,c,b,appendO_st,Function.update_self,adv_st_dst,hd,List.nil_append]
    exact paired_frame packet.word
  · simp only [last,WState.setv_sh,c,b,appendO_sh,Function.update_self,adv_sh_dst hsd,hdh,
      Nat.zero_add,hpairlen,List.length_singleton,frame_length]
  · simp only [last,WState.setv_val,Function.update_of_ne hLS,hcL]
  · simp only [last,WState.setv_val,Function.update_self,hcSC,hcL]
  · simp only [last,WState.setv_val,Function.update_of_ne hSO.symm,c,b,appendO_val,
      Function.update_self,adv_val_OP hOL,hOP,Nat.zero_add,hpairlen,List.length_singleton,frame_length]
  · simp only [last,WState.setv_val,Function.update_of_ne hKS,c,b,appendO_val,
      Function.update_of_ne hKO,adv_val_other _ _ _ K hKO hKL,hK]
  · simp only [last,WState.setv_val,Function.update_of_ne hTS,hcTMP]
  · intro stream hs hd'
    simp only [last,WState.setv_st,WState.setv_sh,c,b,appendO_st,appendO_sh,
      Function.update_of_ne hd',adv_st_other _ _ _ _ hd',adv_sh_other _ _ _ _ hd' hs]
    trivial
  · intro reg hreg
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg
    simp only [last,WState.setv_val,Function.update_of_ne hreg.2.1,c,b,appendO_val,
      Function.update_of_ne hreg.1,adv_val_other _ _ _ reg hreg.1 hreg.2.2.1]

end NearQuarticWires.StagePacket
