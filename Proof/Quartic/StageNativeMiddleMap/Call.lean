import Proof.Quartic.StageNativeMiddleMap.State
import Proof.Wire_3_5.PrimTReadEq

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: one actual
callee execution is followed by physical frame copying, bank erasure
and a return driven by the real copied-byte counter. -/
noncomputable def callProgram (p : Program) : WMX (p.tapeCount+19) 32 :=
  .seq (StagePrint.callAppendProgram (site p) (external p 18) 6)
    (.wm (WM.rewind (external p 18) 6))

def callCost (inputLength budget : ℕ) (output : List Bool) : ℕ :=
  StagePrint.callAppendCost inputLength budget+5*(frame output).length+2

theorem call_exec {Request : Type} {input output : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r=>frame (output r)) budget) (r : Request)
    (cap q count : ℕ) (hc : 2*(input r).length+2+budget r ≤ cap)
    (ho : (frame (output r)).length+1 ≤ cap) :
    ∃ b,WXExec cap (callProgram f.program)
      (prepared f.program cap q (input r) count) b
      (callCost (input r).length (budget r) (output r)) ∧
      SimW (ready f.program cap q (input r) (output r) count) b := by
  let p:=f.program
  let a:=prepared p cap q (input r) count
  have hp (i : Fin 19) : (site p).input≠external p i :=
    bank_external_ne p (NearCubicGates.Close.WorkerArith.inTape p) i
  have ha (i : Fin 19) : a.st (external p i)=(loaded p cap q (input r) count).st (external p i) := by
    simp only [a,prepared,WState.sets_st,Function.update_of_ne (hp i).symm]
  obtain ⟨tapes,steps,b,hs,ec,hb⟩:=StagePrint.callAppend_exec f r cap (site p) (external p 18) 6
    (fun j=>bank_external_ne p j 18) ((external_injective p).ne (by decide))
    ((external_injective p).ne (by decide)) (by change (6 : Fin 32)≠0;decide) a
    (prepared_bank p cap q (input r) count).1 (prepared_bank p cap q (input r) count).2
    (by change a.st (external p 14)=[];rw [ha];rfl) rfl
    (by change a.st (external p 15)=[];rw [ha];rfl) rfl
    (by change NearCubicGates.Close.Worker.Blank (a.st (external p 16));rw [ha];exact nil_blank)
    rfl (fun _=>rfl) ((external_injective p).ne (by decide))
    (by rw [ha];rfl) hc (by simpa [a,prepared,loaded] using ho)
  rw [callPost_eq] at hb
  let c:=copied p cap q (input r) (output r) count
  have hcv : c.val (6 : Fin 32)=(frame (output r)).length := by simp [c,copied,appendO,loaded]
  have hch : c.sh (external p 18)=(frame (output r)).length := by simp [c,copied,appendO,loaded]
  have er:=wrewind_spec cap (external p 18) (6 : Fin 32) (frame (output r)).length c
    hcv (by rw [hcv];omega)
  rw [hch,Nat.sub_self] at er
  obtain ⟨d,ed,hd⟩:=wxexec_sim (WXExec.wm er) b hb
  refine ⟨d,(ec.seq ed).mono ?_,hd⟩
  unfold callCost
  omega

end NearQuarticWires.StageNativeMiddleMap
