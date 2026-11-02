import Proof.Quartic.StagePacketCold.Acquire

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- Step 3 and `lem:print`, paper/paper.tex: duplicate the measured output counter, rewind its
actual tape and physically write every outer marker and delimiter. -/
def measuredFrame (src dst : Fin (ns+1)) (OP SC LEN K TMP : Fin nr) : WM ns nr :=
  .seq (wcopyR LEN K TMP)
    (.seq (WM.rewind src LEN)
      (.seq (cntLoop src SC K (fun bit=>emitPair dst OP bit)) (emitC dst OP false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the outer frame's byte count is the real writer
counter, not a supplied source-size field or a copied giant suffix. -/
theorem measuredFrame_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC LEN K TMP : Fin nr)
    (hsd : src≠dst) (hregs : ([OP,SC,LEN,K,TMP] : List (Fin nr)).Nodup)
    (bits : List Bool) (a : WState ns nr)
    (hin : a.st src=bits) (hhead : a.sh src=bits.length)
    (hout : a.sh dst=(a.st dst).length)
    (hLEN : a.val LEN=bits.length) (hSC : a.val SC=0) (hK : a.val K=0) (hTMP : a.val TMP=0)
    (hcap : a.val OP+4*bits.length+10≤cap) :
    ∃ b,WExec cap (measuredFrame src dst OP SC LEN K TMP) a b (200*bits.length+50) ∧
      b.st dst=a.st dst++frame bits := by
  have hn (i j : Fin 5) (hij : i≠j) :
      ([OP,SC,LEN,K,TMP] : List (Fin nr)).get i≠([OP,SC,LEN,K,TMP] : List (Fin nr)).get j :=
    hregs.injective_get.ne hij
  have hLK : LEN≠K:=hn 2 3 (by decide)
  have hLT : LEN≠TMP:=hn 2 4 (by decide)
  have hKT : K≠TMP:=hn 3 4 (by decide)
  have hOS : OP≠SC:=hn 0 1 (by decide)
  have hOL : OP≠LEN:=hn 0 2 (by decide)
  have hOK : OP≠K:=hn 0 3 (by decide)
  have hSK : SC≠K:=hn 1 3 (by decide)
  have hSL : SC≠LEN:=hn 1 2 (by decide)
  have eCopy:=wcopyR_spec cap LEN K TMP hLK hLT hKT a hK hTMP (by rw [hLEN];omega)
  rw [hLEN] at eCopy
  let b:=a.setv K bits.length
  have hbLEN : b.val LEN=bits.length := by simp [b,Function.update_of_ne hLK,hLEN]
  have eBack:=wrewind_spec cap src LEN bits.length b hbLEN (by omega)
  let c:=(b.setv LEN 0).seth src (b.sh src-bits.length)
  have hcHead : c.sh src=0 := by simp [c,b,hhead]
  have hcK : c.val K=bits.length := by simp [c,b,Function.update_of_ne hLK.symm]
  have hcSC : c.val SC=0 := by simp [c,b,Function.update_of_ne hSL,Function.update_of_ne hSK,hSC]
  have hcOP : c.val OP=a.val OP := by simp [c,b,Function.update_of_ne hOL,Function.update_of_ne hOK]
  have hcOut : c.sh dst=(c.st dst).length := by
    simp only [c,WState.seth_sh,Function.update_of_ne hsd.symm,WState.setv_sh,
      b,WState.setv_sh,WState.seth_st,WState.setv_st]
    exact hout
  have eBits:=cntLoop_spec (cap:=cap) (src:=src) (dst:=dst) (OP:=OP) (SC:=SC)
    hsd hOS (K:=K) hOK.symm hSK.symm (emits_pair (cap:=cap)) [] bits [] c
    (by simpa [c,b] using hin) (by simpa using hcHead) hcOut hcK (by omega)
    (by rw [hcOP,StagePacket.paired_length];omega) (by rw [hcSC];omega)
  let d:=(adv src dst OP SC c (bits.flatMap fun bit=>[true,bit]) bits.length).setv K 0
  have hdOP : d.val OP=a.val OP+2*bits.length := by
    simp only [d,WState.setv_val,Function.update_of_ne hOK,adv_val_OP hOS,
      hcOP,StagePacket.paired_length]
  have hdOut : d.sh dst=(d.st dst).length := by
    simp only [d,WState.setv_sh,WState.setv_st,adv_sh_dst hsd,adv_st_dst,hcOut,List.length_append]
  have eEnd:=NearCubicGates.Close.Codec.emitBit_spec cap dst OP false d hdOut (by rw [hdOP];omega)
  refine ⟨appendO d dst OP [false],(eCopy.seq (eBack.seq (eBits.seq eEnd))).mono (by omega),?_⟩
  simp only [appendO_st,Function.update_self,d,WState.setv_st,adv_st_dst,c,WState.seth_st,
    WState.setv_st,b,WState.setv_st]
  rw [←StagePacket.paired_frame bits,List.append_assoc]

end NearQuarticWires.StageCompiledTerms
