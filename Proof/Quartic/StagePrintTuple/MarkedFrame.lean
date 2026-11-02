import Proof.Quartic.StagePrintTuple.PayloadCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a cached
actual framed field is copied through one literal outer marker layer
while its retained source cursor is reset for later fields. -/
def appendMarkedFrameReset (src dst : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (fun b=>emitPair dst OP b)) (WM.rewind src SC)

/-- `prop:time`, paper/paper.tex: copying all
source frame markers and resetting its cursor are charged linearly. -/
def appendMarkedFrameCost (bits : List Bool) : ℕ := 100*((frame bits).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: every bit of a cached signed constant, coefficient or
unary field is physically written into the cold input record, with no
decoded field or source-length premise. -/
theorem appendMarkedFrameReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (bits rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=frame bits++rest) (hsh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+2*(frame bits).length+1≤cap) :
    WExec cap (appendMarkedFrameReset src dst OP SC) σ
      (appendO σ dst OP (marks (frame bits))) (appendMarkedFrameCost bits) := by
  have e1 := CounterAsm.frameCopy_spec cap hsd hOS
    (emits_pair (cap:=cap) (dst:=dst) (OP:=OP)) (d:=2) (by intro b;simp)
    bits [] rest σ (by simpa using hs) (by simpa using hsh) hd (by omega) (by rw [hSC];omega)
  have hm : (frame bits).flatMap (fun b=>[true,b])=marks (frame bits) := rfl
  rw [hm] at e1
  let d := adv src dst OP SC σ (marks (frame bits)) (frame bits).length
  have hlen : (frame bits).length≤cap := by omega
  have e2 := wrewind_spec cap src SC (frame bits).length d
    (by simp [d,adv,hSC]) (by simpa [d,adv,hSC] using hlen)
  refine (e1.seq e2).cast cap ?_ (by unfold appendMarkedFrameCost;omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst hi;simp [d,adv,appendO,hsd,hsh]
    · simp [d,adv,Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i=SC
    · subst hi;simp [d,adv,appendO,hOS.symm,hSC]
    · simp [d,adv,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageTuple
