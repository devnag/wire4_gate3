import Proof.Quartic.StageTupleSetup.FramePackets
import Proof.Quartic.StagePrintTuple.CoefficientMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
computed width codec is copied from its genuine reply, followed by the
literal fixed coefficient0 or1 and a paid ordinary input frame. -/
def coefficientInputProgram (P : Fin 2↪Fin (ns+1)) (R : Fin 2↪Fin nr)
    (coefficient : ℤ) : WM ns nr :=
  .seq (appendPayloadReset (P 0) (P 1) (R 0) (R 1))
    (.seq (emitWordM (P 1) (R 0) (intWord coefficient))
      (.seq (emitC (P 1) (R 0) false) (WM.rewind (P 1) (R 0))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the real coefficient request contains only its small
width/coefficient packet and preserves the retained width source. -/
theorem coefficientInputProgram_spec (cap : ℕ) (P : Fin 2↪Fin (ns+1)) (R : Fin 2↪Fin nr)
    (L : ℕ) (coefficient : ℤ) (σ : WState ns nr)
    (hs : σ.st (P 0)=frame (natWord L)) (hh : σ.sh (P 0)=0)
    (hd : σ.st (P 1)=[]) (hdh : σ.sh (P 1)=0) (hz : ∀i,σ.val (R i)=0)
    (hcap : 2*(natWord L++intWord coefficient).length+10≤cap) :
    WExec cap (coefficientInputProgram P R coefficient) σ
      (σ.sets (P 1) (frame (CoefficientRequest.mk L coefficient).word))
      (1000*((natWord L++intWord coefficient).length+1)) := by
  have e1:=appendPayloadReset_spec cap (P 0) (P 1) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) (natWord L) [] σ
    (by simpa only [List.append_nil] using hs) hh (by rw [hdh,hd];rfl) (hz 1)
    (by rw [hz 0];simp only [List.length_append] at hcap;omega)
  let a:=appendO σ (P 1) (R 0) (marks (natWord L))
  have e2:=emitWordM_spec cap (P 1) (R 0) (intWord coefficient) a
    (by simp [a,appendO,hdh,hd])
    (by simp only [a,appendO_val,Function.update_self,hz,Codec.marks_length]
        simp only [List.length_append] at hcap;omega)
  let b:=appendO a (P 1) (R 0) (marks (intWord coefficient))
  have e3:=Codec.emitBit_spec cap (P 1) (R 0) false b
    (by simp [b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc])
    (by simp only [b,a,appendO_val,Function.update_self,hz,Codec.marks_length]
        simp only [List.length_append] at hcap;omega)
  let c:=appendO b (P 1) (R 0) [false]
  have hc : c=appendO σ (P 1) (R 0) (frame (natWord L++intWord coefficient)) := by
    simp only [c,b,a,appendO_append,Codec.frame_eq_marks,Streaming.marks_append,List.append_assoc]
  have e4:=wrewind_spec cap (P 1) (R 0) (frame (natWord L++intWord coefficient)).length c
    (by rw [hc];simp [appendO,hz])
    (by rw [hc];simp only [appendO_val,Function.update_self,hz,Nat.zero_add,frame_length];omega)
  refine (e1.seq (e2.seq (e3.seq e4))).cast cap ?_ ?_
  · rw [hc]
    apply WState.eq
    · funext i
      by_cases hi:i=P 1
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd,CoefficientRequest.word]
    · funext i
      by_cases hi:i=R 0
      · subst i;simp [appendO,hz]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · unfold appendPayloadCost
    simp only [List.length_append,frame_length]
    omega

end NearQuarticWires.StageTupleSetup
