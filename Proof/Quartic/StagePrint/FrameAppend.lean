import Proof.Gates.CounterAsm.Copy
import Proof.Quartic.Control.Call

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: append a variable-length framed child stream and reset its source head before reuse. -/
def appendFrameReset (src dst : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (fun b=>emitC dst OP b)) (WM.rewind src SC)

/-- `prop:time`, paper/paper.tex: the framed child copy and source reset have a linear physical clock. -/
def appendFrameCost (bits : List Bool) : ℕ := 45*(frame bits).length+5

/-- `lem:print`, paper/paper.tex: record appending leaves the source word unchanged, its head at zero, and the copy register zero. -/
theorem appendFrameReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (bits rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=frame bits++rest) (hsh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+(frame bits).length+1≤cap) :
    WExec cap (appendFrameReset src dst OP SC) σ (appendO σ dst OP (frame bits))
      (appendFrameCost bits) := by
  have e1:=CounterAsm.frameCopy_spec cap hsd hOS (emits_raw (cap:=cap) (dst:=dst) (OP:=OP))
    (d:=1) (by intro b;simp) bits [] rest σ (by simpa using hs) (by simpa using hsh) hd
    (by omega) (by omega)
  have hcopy : (frame bits).flatMap (fun b=>[b])=frame bits := by simp
  rw [hcopy] at e1
  let τ:=adv src dst OP SC σ (frame bits) (frame bits).length
  have e2:=wrewind_spec cap src SC (frame bits).length τ
    (by simp [τ,adv,hSC]) (by
      have hh : (frame bits).length≤cap := by omega
      simpa [τ,adv,hSC] using hh)
  refine (WExec.seq e1 e2).cast cap ?_ (by unfold appendFrameCost;omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst hi
      simp [τ,adv,appendO,hsd,hsh]
    · simp [τ,adv,Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i=SC
    · subst hi
      simp [τ,adv,appendO,hOS.symm,hSC]
    · simp [τ,adv,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StagePrint
