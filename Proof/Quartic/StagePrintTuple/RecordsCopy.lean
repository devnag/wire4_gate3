import Proof.Quartic.StagePrintTuple.PayloadCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: every actual
nonempty fixed-field record is copied once, stopping at the blank after
the record stream and resetting the source by its real scanned length. -/
def appendRecordsReset (src dst : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameLoop src SC (fun b=>emitC dst OP b)) (WM.rewind src SC)

/-- `prop:time`, paper/paper.tex: actual raw
record copying and its source rewind have a linear physical clock. -/
def appendRecordsCost (records : List (List Bool)) : ℕ :=
  60*((records.flatMap frame).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual raw fixed-field stream is self-delimiting
when every field has positive width. The copy reads its real record
markers, not an inferred callee output-length or child-count field. -/
theorem appendRecordsReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (records : List (List Bool)) (rest : List Bool)
    (hne : ∀ record∈records,record≠[]) (hend : rest.headD false=false)
    (σ : WState ns nr) (hs : σ.st src=records.flatMap frame++rest)
    (hsh : σ.sh src=0) (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+(records.flatMap frame).length+1≤cap) :
    WExec cap (appendRecordsReset src dst OP SC) σ
      (appendO σ dst OP (records.flatMap frame)) (appendRecordsCost records) := by
  have e1 := CounterAsm.frameLoop_spec cap hsd hOS
    (emits_raw (cap:=cap) (dst:=dst) (OP:=OP)) (d:=1) (by intro b;simp)
    rest hend records [] σ hne (by simpa using hs) (by simpa using hsh) hd
    (by omega) (by rw [hSC];omega)
  have hcopy : (records.flatMap frame).flatMap (fun b=>[b])=records.flatMap frame := by simp
  rw [hcopy] at e1
  let τ := adv src dst OP SC σ (records.flatMap frame) (records.flatMap frame).length
  have hlen : (records.flatMap frame).length≤cap := by omega
  have e2 := wrewind_spec cap src SC (records.flatMap frame).length τ
    (by simp only [τ,adv,WState.setv_val,Function.update_self,hSC,Nat.zero_add])
    (by simpa only [τ,adv,WState.setv_val,Function.update_self,hSC,Nat.zero_add] using hlen)
  refine (e1.seq e2).cast cap ?_ (by unfold appendRecordsCost;omega)
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

end NearQuarticWires.StageTuple
