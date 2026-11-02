import Proof.Gates.CounterAsm.Copy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: an
arbitrarily large target-width codec is copied byte for byte and its
source cursor reset, without decoding its numerical value. -/
def copyRawNaturalReset (src dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (CounterAsm.natCopy src SC K (fun b=>emitC dst OP b)) (WM.rewind src SC)

/-- `lem:print` and `prop:time`, paper/paper.tex: the retained binary target-width field costs
only its actual encoded length and preserves every other scalar. -/
theorem copyRawNaturalReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (value : ℕ) (rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=natWord value++rest) (hsh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0) (hK : σ.val K=0)
    (hcap : σ.val OP+(natWord value).length+1≤cap) :
    WExec cap (copyRawNaturalReset src dst OP SC K) σ
      (appendO σ dst OP (natWord value)) (60*((natWord value).length+1)) := by
  have hn : 1≤(natWord value).length:=by rw [CounterAsm.natWord_len];omega
  have e1:=CounterAsm.natCopy_spec cap hsd hOS hKO hKS
    (emits_raw (cap:=cap) (dst:=dst) (OP:=OP)) (d:=1) (by intro b;simp)
    value [] rest σ (by simpa using hs) (by simpa using hsh) hd hK
    (by omega) (by rw [hSC];omega) (by omega)
  have he : (natWord value).flatMap (fun b=>[b])=natWord value:=by simp
  rw [he] at e1
  let d:=adv src dst OP SC σ (natWord value) (natWord value).length
  have hlen : (natWord value).length≤cap:=by omega
  have e2:=wrewind_spec cap src SC (natWord value).length d
    (by simp only [d,adv,WState.setv_val,Function.update_self,hSC,Nat.zero_add])
    (by simpa only [d,adv,WState.setv_val,Function.update_self,hSC,Nat.zero_add] using hlen)
  refine (e1.seq e2).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi:i=src
      · subst hi;simp [d,adv,appendO,hsd,hsh]
      · simp [d,adv,Function.update_of_ne hi]
    · rfl
    · funext i
      by_cases hi:i=SC
      · subst hi;simp [d,adv,appendO,hOS.symm,hSC]
      · simp [d,adv,Function.update_of_ne hi]
    · rfl
  · omega

end NearQuarticWires.StageNativeKidsPool
