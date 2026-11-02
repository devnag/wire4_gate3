import Proof.Quartic.StageNativeMiddleMap.State

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: only the
genuine framed middle field is copied into the actual cold call bank;
the measured byte counter returns its head before execution. -/
def prepareProgram (p : Program) : WMX (p.tapeCount+19) 32 :=
  .seq (.wm (StagePrint.appendFrameReset (external p 3) (site p).input 4 5))
    (.wm (WM.rewind (site p).input 4))

theorem prepare_exec (p : Program) (cap q : ℕ) (input : List Bool) (count : ℕ)
    (hc : (frame input).length+1 ≤ cap) :
    WXExec cap (prepareProgram p) (loaded p cap q input count)
      (prepared p cap q input count) (50*(frame input).length+10) := by
  let a:=loaded p cap q input count
  have hbs : (site p).input≠external p 3 :=
    bank_external_ne p (NearCubicGates.Close.WorkerArith.inTape p) 3
  have hb : a.st (site p).input=[] := loaded_bank p cap q input count _
  have e1:=StagePrint.appendFrameReset_spec cap (external p 3) (site p).input (4 : Fin 32) 5
    hbs.symm (by decide) input [] a (by simp [a,loaded,external,fields]) rfl
    (by rw [hb];rfl) rfl (by simpa only [a,loaded,Nat.zero_add] using hc)
  let b:=appendO a (site p).input (4 : Fin 32) (frame input)
  have hbv : b.val (4 : Fin 32)=(frame input).length := by
    simp only [b,appendO_val,Function.update_self,a,loaded,Nat.zero_add]
  have e2:=wrewind_spec cap (site p).input (4 : Fin 32) (frame input).length b
    hbv (by rw [hbv];omega)
  have hbsh : b.sh (site p).input=(frame input).length := by simp [b,appendO,a,loaded]
  rw [hbsh,Nat.sub_self] at e2
  refine ((WXExec.wm e1).seq (WXExec.wm e2)).cast cap ?_ (by unfold StagePrint.appendFrameCost;omega)
  apply WState.eq
  · funext i
    by_cases hi : i=(site p).input
    · subst i;rfl
    · simp [b,appendO,prepared,a,loaded,Function.update_of_ne hi]
  · simp [b,appendO,prepared,a,hb]
  · funext i
    by_cases hi : i=(4 : Fin 32)
    · subst i;rfl
    · simp [b,appendO,prepared,a,loaded,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageNativeMiddleMap
