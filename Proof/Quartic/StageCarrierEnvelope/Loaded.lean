import Proof.Quartic.StageCarrierEnvelope.Fields
import Proof.Quartic.StageCarrierEnvelope.Data

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns : ℕ}

/-- `lem:print`, paper/paper.tex: the three
actual fields and eight empty slots have the fixed native record layout. -/
def envelopeWord (q count : ℕ) (bits : List Bool) : List Bool :=
  Top.loadRec (natWord q) (frame bits) (natWord count) [] [] [] [] [] [] [] []

theorem frame_envelopeWord (q count : ℕ) (bits : List Bool) :
    frame (envelopeWord q count bits)=
      marks (frame (natWord q))++marks (frame (frame bits))++marks (frame (natWord count))++
        marks (List.replicate 8 false)++[false] := by
  have hw : envelopeWord q count bits=
      frame (natWord q)++frame (frame bits)++frame (natWord count)++List.replicate 8 false := by
    simp only [envelopeWord,Top.loadRec,NearCubicGates.Close.Codec.frame_eq_marks,
      marks,List.flatMap_nil,List.nil_append,List.replicate_succ,List.replicate_zero,List.append_assoc]
    rfl
  rw [hw,NearCubicGates.Close.Codec.frame_eq_marks]
  simp only [Streaming.marks_append,List.append_assoc]

theorem quad_length (bits : List Bool) : (bits.flatMap quad).length=4*bits.length := by
  induction bits with
  | nil=>rfl
  | cons bit tail ih=>simp only [List.flatMap_cons,List.length_append,quad,List.length_cons,List.length_nil,ih];omega

/-- `lem:print`, paper/paper.tex: fixed control
copies the actual first modulus, one original carrier and the actual
column reply, then seals the immutable ordinary record. -/
def loadedEnvelope (P : Fin 4↪Fin (ns+1)) : WM ns 16 :=
  .seq (copyModulusField (P 0) (P 3) 1 0 2)
    (.seq (copyCarrierField (P 1) (P 3) 1 0)
      (.seq (copyColumnField (P 2) (P 3) 1 0) (sealEnvelope (P 3) 1)))

/-- `lem:print` and `prop:time`, paper/paper.tex: source cursors and the measured prefixes determine all
three physical copies; the complete source occurs in exactly one field. -/
theorem loadedEnvelope_run (cap : ℕ) (P : Fin 4↪Fin (ns+1))
    (q count : ℕ) (bits pre rest : List Bool) (a : WState ns 16)
    (hq : a.st (P 0)=pre++natWord q++rest) (hqhead : a.sh (P 0)=pre.length)
    (hb : a.st (P 1)=frame bits) (hbhead : a.sh (P 1)=0)
    (hn : a.st (P 2)=frame (natWord count)) (hnhead : a.sh (P 2)=0)
    (ho : a.st (P 3)=[]) (hohead : a.sh (P 3)=0)
    (hOP : a.val 1=0) (hK : a.val 2=0)
    (hc : a.val 0+8*((natWord q).length+(frame bits).length+(frame (natWord count)).length+10)≤cap) :
    ∃ b, WExec cap (loadedEnvelope P) a b
      (1000*((natWord q).length+(frame bits).length+(frame (natWord count)).length+1)) ∧
      b.st (P 3)=frame (envelopeWord q count bits) := by
  have hp {i j : Fin 4} : P i=P j ↔ i=j := P.injective.eq_iff
  have e1:=copyModulusField_run cap (P 0) (P 3) (1 : Fin 16) 0 2
    (P.injective.ne (by decide)) (by decide) (by decide) (by decide)
    q pre rest a hq hqhead (by rw [ho,hohead];rfl) hK
    (by rw [hOP];omega) (by omega)
  let b:=appendO (adv (P 0) (P 3) (1 : Fin 16) 0 a ((natWord q).flatMap quad) (natWord q).length)
    (P 3) 1 [true,false]
  have hbout : b.st (P 3)=marks (frame (natWord q)) := by
    simp only [b,appendO_st,Function.update_self,adv_st_dst,ho,List.nil_append]
    exact quad_frame _
  have e2:=copyCarrierField_run cap (P 1) (P 3) (1 : Fin 16) 0
    (P.injective.ne (by decide)) (by decide) bits [] [] b
    (by simp [b,adv,appendO,hp,hb]) (by simp [b,adv,appendO,hp,hbhead])
    (by simp [b,adv,appendO,hp,hohead,ho,List.length_append])
    (by simp only [b,appendO_val,Function.update_self,adv_val_OP (by decide : (1 : Fin 16)≠0),hOP,quad_length,List.length_cons,List.length_nil];omega)
    (by simp only [b,appendO_val,Function.update_of_ne (by decide : (0 : Fin 16)≠1),adv_val_SC];omega)
  let c:=appendO (adv (P 1) (P 3) (1 : Fin 16) 0 b ((frame bits).flatMap quad) (frame bits).length)
    (P 3) 1 [true,false]
  have hcout : c.st (P 3)=marks (frame (natWord q))++marks (frame (frame bits)) := by
    simp only [c,appendO_st,Function.update_self,adv_st_dst,hbout,List.append_assoc]
    rw [quad_frame]
  have e3:=copyColumnField_run cap (P 2) (P 3) (1 : Fin 16) 0
    (P.injective.ne (by decide)) (by decide) (natWord count) [] [] c
    (by simp [c,b,adv,appendO,hp,hn]) (by simp [c,b,adv,appendO,hp,hnhead])
    (by simp [c,b,adv,appendO,hp,hohead,ho,List.length_append,Nat.add_assoc];omega)
    (by simp only [c,b,appendO_val,Function.update_self,adv_val_OP (by decide : (1 : Fin 16)≠0),hOP,quad_length,List.length_cons,List.length_nil];omega)
    (by simp only [c,b,appendO_val,Function.update_of_ne (by decide : (0 : Fin 16)≠1),adv_val_SC];omega)
  let d:=adv (P 2) (P 3) (1 : Fin 16) 0 c (marks (frame (natWord count))) (frame (natWord count)).length
  have e4:=sealEnvelope_run cap (P 3) (1 : Fin 16) d
    (by simp [d,c,b,adv,appendO,hp,hohead,ho,List.length_append,Nat.add_assoc];omega)
    (by simp only [d,c,b,adv_val_OP (by decide : (1 : Fin 16)≠0),appendO_val,Function.update_self,hOP,
      quad_length,Streaming.marks_length,List.length_cons,List.length_nil];omega)
  let last:=appendO (appendO d (P 3) (1 : Fin 16) (marks (List.replicate 8 false))) (P 3) 1 [false]
  refine ⟨last,(e1.seq (e2.seq (e3.seq e4))).mono (by omega),?_⟩
  simp only [last,d,appendO_st,Function.update_self,adv_st_dst,hcout,frame_envelopeWord,List.append_assoc]

end NearQuarticWires.StageCarrierEnvelope
