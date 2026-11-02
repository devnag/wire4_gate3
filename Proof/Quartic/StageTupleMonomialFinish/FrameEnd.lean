import Proof.Quartic.StagePrintTuple.FrameErase

set_option autoImplicit false

namespace NearQuarticWires.StageTupleMonomialFinish

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the support
cursor scans the actual remaining framed tail and clears its scan
counter, without resetting or rescanning the parsed count prefix. -/
def finishFrameCursor (src : Fin (ns+1)) (SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (fun _=>WM.skip)) (WM.clear SC)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual finite frame-tail scan reaches its physical
end in time linear in that tail, preserving all bytes and counters. -/
theorem finishFrameCursor_spec (cap : ℕ) (src dummy : Fin (ns+1)) (SC OP : Fin nr)
    (hsd : src≠dummy) (hOS : OP≠SC) (bits pre rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=pre++frame bits++rest) (hh : σ.sh src=pre.length)
    (hd : σ.sh dummy=(σ.st dummy).length) (ho : σ.val OP≤cap) (hSC : σ.val SC=0)
    (hcap : (frame bits).length≤cap) :
    WExec cap (finishFrameCursor src SC) σ
      (σ.seth src (pre.length+(frame bits).length)) (40*((frame bits).length+1)) := by
  have e1 := CounterAsm.frameCopy_spec cap hsd hOS
    (emits_none (cap:=cap) (dst:=dummy) (OP:=OP)) (d:=0) (by intro b;simp)
    bits pre rest σ hs hh hd (by simpa using ho) (by rw [hSC];omega)
  have hz : (frame bits).flatMap (fun _=>([]:List Bool))=[] := by simp
  rw [hz] at e1
  let a := adv src dummy OP SC σ [] (frame bits).length
  have e2 := wclear_spec cap SC (frame bits).length a
    (by simp [a,adv,hSC])
    (by simpa only [a,adv_val_SC,hSC,Nat.zero_add] using hcap)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi:i=src
    · subst i;simp [a,adv,appendO,hh]
    · simp [a,adv,appendO,Function.update_of_ne hi]
  · simp [a,adv,appendO]
  · funext i
    by_cases hi:i=SC
    · subst i;simp [a,adv,appendO,hSC]
    · simp [a,adv,appendO,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageTupleMonomialFinish
