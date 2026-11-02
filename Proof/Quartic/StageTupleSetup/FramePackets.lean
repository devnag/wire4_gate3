import Proof.Quartic.StagePrintTuple.ContextFrame
import Proof.Quartic.StagePrintTuple.MarkedFrame
import Proof.Quartic.StagePrintTuple.PayloadAt
import Proof.Wire_3_5.PrimAsmCopyNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one retained
small natural codec is framed by its physical bits, without decoding its
value or inspecting the complete source/Terms stream. -/
def frameNaturalProgram (P : Fin 2↪Fin (ns+1)) (R : Fin 3↪Fin nr) : WM ns nr :=
  .seq (appendNaturalsReset 1 (P 0) (P 1) (R 0) (R 1) (R 2))
    (.seq (emitC (P 1) (R 0) false) (WM.rewind (P 1) (R 0)))

theorem frameNaturalProgram_spec (cap : ℕ) (P : Fin 2↪Fin (ns+1)) (R : Fin 3↪Fin nr)
    (value : ℕ) (σ : WState ns nr)
    (hs : σ.st (P 0)=natWord value) (hh : σ.sh (P 0)=0)
    (hd : σ.st (P 1)=[]) (hdh : σ.sh (P 1)=0) (hz : ∀i,σ.val (R i)=0)
    (hcap : 2*(natWord value).length+2≤cap) :
    WExec cap (frameNaturalProgram P R) σ (σ.sets (P 1) (frame (natWord value)))
      (1000*((natWord value).length+1)) := by
  have e1:=appendNaturalsReset_spec cap (P 0) (P 1) (R 0) (R 1) (R 2)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) [value] [] σ (by simpa using hs) hh
    (by rw [hdh,hd];rfl) (hz 1) (hz 2) (by
      rw [hz 0]
      simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
      omega)
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_cons,List.length_nil] at e1
  let a:=appendO σ (P 1) (R 0) (marks (natWord value))
  have e2:=Codec.emitBit_spec cap (P 1) (R 0) false a
    (by simp [a,appendO,hdh,hd])
    (by simp only [a,appendO_val,Function.update_self,hz,Codec.marks_length];omega)
  let b:=appendO a (P 1) (R 0) [false]
  have hb : b=appendO σ (P 1) (R 0) (frame (natWord value)) := by
    simp only [b,a,appendO_append,Codec.frame_eq_marks]
  have e3:=wrewind_spec cap (P 1) (R 0) (frame (natWord value)).length b
    (by rw [hb];simp [appendO,hz])
    (by rw [hb];simp only [appendO_val,Function.update_self,hz,Nat.zero_add,frame_length];omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ ?_
  · rw [hb]
    apply WState.eq
    · funext i
      by_cases hi:i=P 1
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd]
    · funext i
      by_cases hi:i=R 0
      · subst i;simp [appendO,hz]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · unfold appendNaturalsCost
    simp only [List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,frame_length]
    omega

/-- `lem:print`, paper/paper.tex: the actual
retained row-count header already has its inner frame. Add only the
ordinary callee-input frame by actual marked copying and head reset. -/
def frameRetainedProgram (P : Fin 2↪Fin (ns+1)) (R : Fin 2↪Fin nr) : WM ns nr :=
  .seq (appendMarkedFrameReset (P 0) (P 1) (R 0) (R 1))
    (.seq (emitC (P 1) (R 0) false) (WM.rewind (P 1) (R 0)))

theorem frameRetainedProgram_spec (cap : ℕ) (P : Fin 2↪Fin (ns+1)) (R : Fin 2↪Fin nr)
    (bits : List Bool) (σ : WState ns nr)
    (hs : σ.st (P 0)=frame bits) (hh : σ.sh (P 0)=0)
    (hd : σ.st (P 1)=[]) (hdh : σ.sh (P 1)=0) (hz : ∀i,σ.val (R i)=0)
    (hcap : 2*(frame bits).length+2≤cap) :
    WExec cap (frameRetainedProgram P R) σ (σ.sets (P 1) (frame (frame bits)))
      (1000*((frame bits).length+1)) := by
  have hframeLen:=frame_length bits
  have e1:=appendMarkedFrameReset_spec cap (P 0) (P 1) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) bits [] σ
    (by simpa only [List.append_nil] using hs) hh (by rw [hdh,hd];rfl) (hz 1)
    (by rw [hz 0];omega)
  let a:=appendO σ (P 1) (R 0) (marks (frame bits))
  have e2:=Codec.emitBit_spec cap (P 1) (R 0) false a
    (by simp [a,appendO,hdh,hd])
    (by simp only [a,appendO_val,Function.update_self,hz,Codec.marks_length];omega)
  let b:=appendO a (P 1) (R 0) [false]
  have hb : b=appendO σ (P 1) (R 0) (frame (frame bits)) := by
    simp only [b,a,appendO_append,Codec.frame_eq_marks]
  have e3:=wrewind_spec cap (P 1) (R 0) (frame (frame bits)).length b
    (by rw [hb];simp [appendO,hz])
    (by rw [hb];simp only [appendO_val,Function.update_self,hz,Nat.zero_add,frame_length];omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ ?_
  · rw [hb]
    apply WState.eq
    · funext i
      by_cases hi:i=P 1
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd]
    · funext i
      by_cases hi:i=R 0
      · subst i;simp [appendO,hz]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · unfold appendMarkedFrameCost
    simp only [frame_length]
    omega

end NearQuarticWires.StageTupleSetup
