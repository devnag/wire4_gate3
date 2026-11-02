import Proof.Quartic.StagePacket.PacketBody
import Proof.Quartic.StageGreedyCollector.Entry

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

open StagePacket

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: copy the three
actual scalar codecs and the following framed signed Terms payload. -/
def copyEntryBody (src dst : Fin (ns+1)) (OP LEN K : Fin nr) : WM ns nr :=
  .seq (copyNaturalFields src LEN K (fun bit=>emitPair dst OP bit) 3)
    (frameCopy src LEN (fun bit=>emitPair dst OP bit))

/-- `lem:print` and `prop:time`, paper/paper.tex: packet copying stops after the real payload frame,
measures exactly its consumed source bytes and never scans the suffix. -/
theorem copyEntryBody_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP LEN K : Fin nr)
    (hsd : src≠dst) (hOL : OP≠LEN) (hKO : K≠OP) (hKL : K≠LEN)
    (packet : Entry) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++packet.word++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (hK : a.val K=0)
    (houtputCap : a.val OP+2*packet.word.length≤cap)
    (hsourceCap : a.val LEN+packet.word.length≤cap) :
    WExec cap (copyEntryBody src dst OP LEN K) a
      (adv src dst OP LEN a (packet.word.flatMap fun bit=>[true,bit]) packet.word.length)
      (28*(packet.header.flatMap NearCubicWires.RepairRepresentation.natWord).length+
        55*(frame packet.payload).length+4) := by
  let header:=packet.header.flatMap NearCubicWires.RepairRepresentation.natWord
  let payload:=frame packet.payload
  have hword : packet.word=header++payload := rfl
  have hheadSource : a.st src=pre++header++(payload++suffix) := by
    simpa only [hword,List.append_assoc] using hsource
  have hlength : packet.word.length=header.length+payload.length := by rw [hword,List.length_append]
  have hheadOutput : a.val OP+2*header.length≤cap := by rw [hlength] at houtputCap;nlinarith
  have hheadInput : a.val LEN+header.length≤cap := by rw [hlength] at hsourceCap;omega
  have eHead:=copyNaturalFields_spec cap src dst OP LEN K hsd hOL hKO hKL
    (fun bit=>emitPair dst OP bit) (fun bit=>[true,bit]) 15 2 (emits_pair (cap:=cap))
    (by intro bit;simp) packet.header pre (payload++suffix) a hheadSource hhead hout hK
    hheadOutput hheadInput
  have hfields : packet.header.length=3 := by simp [Entry.header]
  rw [hfields] at eHead
  let b:=adv src dst OP LEN a (header.flatMap fun bit=>[true,bit]) header.length
  have hbsource : b.st src=(pre++header)++frame packet.payload++suffix := by
    rw [adv_st_src hsd,hsource,hword]
    simp only [payload,List.append_assoc]
  have hbhead : b.sh src=(pre++header).length := by rw [adv_sh_src,hhead,List.length_append]
  have hbout : b.sh dst=(b.st dst).length := by rw [adv_sh_dst hsd,adv_st_dst,hout,List.length_append]
  have hfront : (header.flatMap fun bit=>[true,bit]).length=2*header.length := paired_length header
  have hframeInput : b.val LEN+(frame packet.payload).length≤cap := by
    rw [adv_val_SC]
    rw [hlength] at hsourceCap
    simpa only [payload,Nat.add_assoc] using hsourceCap
  have ePayload:=frameCopy_spec cap hsd hOL (emits_pair (cap:=cap))
    (d:=2) (by intro bit;simp) packet.payload (pre++header) suffix b hbsource hbhead hbout
    (by rw [adv_val_OP hOL,hfront];rw [hlength] at houtputCap;nlinarith)
    (by omega)
  refine WExec.cast cap (WExec.seq eHead ePayload) ?_ ?_
  · rw [adv_adv hsd hOL]
    simp only [hword,payload,List.flatMap_append,List.length_append]
  · dsimp only [header,payload] at *
    omega

end NearQuarticWires.StageGreedyCollector
