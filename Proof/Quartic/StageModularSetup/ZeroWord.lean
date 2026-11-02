import Proof.Quartic.StageModularSetup.Stride
import Proof.Quartic.StagePacket.Isolation
import Proof.Wire_3_5.CompilerMachinePoolConv

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageModularCuts

/-- `lem:print`, paper/paper.tex: the actual
repeated marker/data block represents precisely a fixed-width zero word. -/
theorem zeroWord_bits (width : ℕ) : reps width [true,false]++[false]=frame (binary width 0) := by
  have hp : reps width [true,false]=(List.replicate width false).flatMap fun bit=>[true,bit] := by
    induction width with
    | zero=>rfl
    | succ width ih=>
      rw [reps_succ,ih,List.replicate_succ',List.flatMap_append]
      rfl
  rw [hp,StagePacket.paired_frame,Pool.binary_zero']

/-- `lem:print`, paper/paper.tex: emit a real
zero work word from the retained width and return its output head. -/
def initializeZeroWord (output : Fin 16) : WM 15 16 :=
  .seq (repRegW output 11 7 3 4 [true,false])
    (.seq (emitC output 11 false) (WM.rewind output 11))

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed-width work word is physically initialized,
with all output/count scratch and its real head restored to zero. -/
theorem initializeZeroWord_spec (cap : ℕ) (output : Fin 16) (width : ℕ) (a : State)
    (hword : a.st output=[]) (hhead : a.sh output=0)
    (hwidth : a.val 7=width) (h3 : a.val 3=0) (h4 : a.val 4=0) (h11 : a.val 11=0)
    (hcap : 2*width+1≤cap) :
    WExec cap (initializeZeroWord output) a
      (a.sets output (frame (binary width 0))) (60*width+40) := by
  have eZeros:=repRegW_spec cap output (11 : Fin 16) 7 3 4
    (by decide) (by decide) (by decide) (by decide) [true,false] a h3 h4
    (by rw [hword,hhead];rfl) (by rw [hwidth];omega) (by rw [h11,hwidth];simp;omega)
  rw [hwidth] at eZeros
  let b:=appendO a output 11 (reps width [true,false])
  have hbits : (reps width [true,false]).length=2*width := by
    unfold reps
    simp
    omega
  have hb11 : b.val 11=2*width := by simp only [b,appendO_val,Function.update_self,h11,hbits,Nat.zero_add]
  have hbHead : b.sh output=(b.st output).length := by simp [b,hword,hhead]
  have eMark:=NearCubicGates.Close.Codec.emitBit_spec cap output (11 : Fin 16) false b hbHead
    (by rw [hb11];omega)
  let c:=appendO b output 11 [false]
  have hc11 : c.val 11=2*width+1 := by simp [c,hb11]
  have eRewind:=wrewind_spec cap output (11 : Fin 16) (2*width+1) c hc11 (by rw [hc11];exact hcap)
  refine (eZeros.seq (eMark.seq eRewind)).cast cap ?_ (by norm_num;omega)
  apply WState.eq
  · funext stream
    by_cases hs : stream=output
    · subst stream;simp [c,b,appendO,hhead,hbits]
    · simp [c,b,appendO,hs]
  · funext stream
    by_cases hs : stream=output
    · subst stream
      simp only [WState.seth_st,WState.setv_st,c,appendO_st,Function.update_self,b,hword,List.nil_append,
        WState.sets_st]
      exact zeroWord_bits width
    · simp [c,b,appendO,hs]
  · funext reg
    by_cases hr : reg=11
    · subst reg;simp [h11]
    · simp [c,b,appendO,hr]
  · rfl

end NearQuarticWires.StageModularSetup
