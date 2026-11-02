import Proof.Quartic.StageModularSetup.ZeroWord
import Proof.Gates.CounterAsm.Copy
import Proof.Quartic.StageResize.BinaryPadding

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Recovery.HTParts
open StageModularCuts

/-- `lem:print`, paper/paper.tex: copying the
actual low-first binary tail and its computed zero padding gives the
exact bounded modulus word, including the extra boundary work bit. -/
theorem modulus_bits (width q : ℕ) (hwidth : natBitLength q≤width) :
    ((binary (natBitLength q) q).flatMap fun bit=>[true,bit])++
      reps (width-natBitLength q) [true,false]++[false]=frame (binary width q) := by
  rw [List.append_assoc,zeroWord_bits,Pool.binary_zero']
  rw [StageResize.binary_zero_extension (Pool.lt_pow_natBitLength q) hwidth]
  exact (Pool.frame_append' _ _).symm

/-- `lem:print`, paper/paper.tex: copy the
bounded binary tail, pad its actual work width, and return both heads. -/
def writeModulusTail : WM 15 16 :=
  .seq (cntLoop 2 1 3 (fun bit=>emitPair 7 11 bit))
    (.seq (repW 7 11 9 [true,false])
      (.seq (emitC 7 11 false) (.seq (WM.rewind 2 1) (WM.rewind 7 11))))

/-- `lem:print`, paper/paper.tex: all parsed
length and padding counters are consumed and the actual binary modulus
source is returned to its original zero head. -/
def modulusTailState (a : State) (width q : ℕ) : State :=
  (((((a.sets 7 (frame (binary width q))).seth 2 0).setv 1 0).setv 3 0).setv 9 0).setv 11 0

/-- `lem:print` and `prop:time`, paper/paper.tex: binary modulus copying touches only the original
modulus codec and its new bounded work tape; the signed cut stream is
never scanned, and no loop uses the modulus's numeric value. -/
theorem writeModulusTail_spec (cap width q : ℕ) (a : State)
    (hsource : a.st 2=natWord q) (hhead : a.sh 2=natBitLength q+1)
    (hword : a.st 7=[]) (houtputHead : a.sh 7=0)
    (h1 : a.val 1=natBitLength q+1) (h3 : a.val 3=natBitLength q)
    (h9 : a.val 9=width-natBitLength q) (h11 : a.val 11=0)
    (hwidth : natBitLength q≤width) (hcap : 4*width+10≤cap) :
    WExec cap writeModulusTail a (modulusTailState a width q) (200*(width+1)) := by
  let len:=natBitLength q
  let bits:=binary len q
  let preBits:=List.replicate len true++[false]
  have hbits : bits.length=len := binary_length _ _
  have eCopy:=cntLoop_spec (cap:=cap) (src:=(2 : Fin 16)) (dst:=7) (OP:=(11 : Fin 16)) (SC:=1)
    (by decide) (by decide) (K:=3) (by decide) (by decide) (emits_pair (cap:=cap)) [] bits preBits a
    (by
      rw [hsource,Pool.natWord_eq]
      simp only [preBits,bits,len,List.append_nil,List.singleton_append,List.append_assoc])
    (by simpa only [preBits,List.length_append,List.length_replicate,List.length_singleton] using hhead)
    (by rw [hword,houtputHead];rfl) (by rw [h3,hbits]) (by rw [hbits];omega)
    (by rw [h11,StagePacket.paired_length,hbits];omega) (by rw [h1,hbits];omega)
  let b:=(adv (2 : Fin 16) 7 (11 : Fin 16) 1 a (bits.flatMap fun bit=>[true,bit]) len).setv 3 0
  have hb11 : b.val 11=2*len := by
    simp only [b,WState.setv_val,Function.update_of_ne (by decide : (11 : Fin 16)≠3),
      adv_val_OP (by decide : (11 : Fin 16)≠1),h11,Nat.zero_add,StagePacket.paired_length,hbits]
  have hb9 : b.val 9=width-len := by
    simp only [b,WState.setv_val,Function.update_of_ne (by decide : (9 : Fin 16)≠3),
      adv_val_other _ _ _ _ (by decide : (9 : Fin 16)≠11) (by decide : (9 : Fin 16)≠1),h9]
    rfl
  have hb1 : b.val 1=2*len+1 := by
    simp only [b,WState.setv_val,Function.update_of_ne (by decide : (1 : Fin 16)≠3),adv_val_SC,h1]
    dsimp only [len]
    omega
  have hbOut : b.sh 7=(b.st 7).length := by
    simp only [b,WState.setv_sh,WState.setv_st,adv_sh_dst (by decide : (2 : Fin 16)≠7),
      adv_st_dst,hword,houtputHead,List.nil_append,Nat.zero_add]
  have ePad:=repW_spec cap (7 : Fin 16) (11 : Fin 16) 9 (by decide) [true,false] (width-len) b hb9 hbOut
    (by rw [hb11];norm_num;omega) (by omega)
  let c:=(appendO b 7 11 (reps (width-len) [true,false])).setv 9 0
  have hpairs : (reps (width-len) [true,false]).length=2*(width-len) := by unfold reps;simp;omega
  have hc11 : c.val 11=2*width := by
    simp only [c,WState.setv_val,Function.update_of_ne (by decide : (11 : Fin 16)≠9),
      appendO_val,Function.update_self,hb11,hpairs]
    dsimp only [len]
    omega
  have hcOut : c.sh 7=(c.st 7).length := by
    simp only [c,WState.setv_sh,WState.setv_st,appendO_sh,appendO_st,Function.update_self,hbOut,
      List.length_append]
  have eMark:=NearCubicGates.Close.Codec.emitBit_spec cap (7 : Fin 16) (11 : Fin 16) false c hcOut
    (by rw [hc11];omega)
  let d:=appendO c 7 11 [false]
  have hd1 : d.val 1=2*len+1 := by simp [d,c,hb1]
  have hd11 : d.val 11=2*width+1 := by simp [d,hc11]
  have eSource:=wrewind_spec cap (2 : Fin 16) (1 : Fin 16) (2*len+1) d hd1 (by rw [hd1];omega)
  let e:=(d.setv 1 0).seth 2 (d.sh 2-(2*len+1))
  have he11 : e.val 11=2*width+1 := by simp [e,hd11]
  have eOutput:=wrewind_spec cap (7 : Fin 16) (11 : Fin 16) (2*width+1) e he11 (by rw [he11];omega)
  rw [hbits] at eCopy
  refine (eCopy.seq (ePad.seq (eMark.seq (eSource.seq eOutput)))).cast cap ?_ ?_
  · apply WState.eq
    · funext stream
      by_cases hs2 : stream=2
      · subst stream
        simp [e,d,c,b,modulusTailState,adv,appendO,hhead,len]
        omega
      · by_cases hs7 : stream=7
        · subst stream
          simp [e,d,c,b,modulusTailState,adv,appendO,houtputHead,hbits,hpairs]
          dsimp only [len]
          omega
        · simp [e,d,c,b,modulusTailState,adv,appendO,hs2,hs7]
    · funext stream
      by_cases hs7 : stream=7
      · subst stream
        simp only [WState.seth_st,WState.setv_st,e,d,c,b,appendO_st,Function.update_self,adv_st_dst,
          modulusTailState,WState.sets_st,hword,List.nil_append]
        exact modulus_bits width q hwidth
      · simp [e,d,c,b,modulusTailState,adv,appendO,hs7]
    · funext reg
      fin_cases reg <;> simp [e,d,c,b,modulusTailState,adv,appendO,h11]
    · rfl
  · norm_num only [List.length_cons,List.length_nil]
    dsimp only [len] at *
    omega

end NearQuarticWires.StageModularSetup
