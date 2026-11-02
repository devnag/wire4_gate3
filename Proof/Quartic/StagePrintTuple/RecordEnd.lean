import Proof.Quartic.StagePrintTuple.RecordsCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a tuple
pool cursor advances through its current actual record segment,
reaching its real final blank without consuming an additional source
cell or copying its already parsed count prefix. -/
def finishRecordCursor (src : Fin (ns+1)) (SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameLoop src SC (fun _=>WM.skip)) (WM.clear SC)

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete physical end scan depends only on the
current tuple segment. Its real scanned-byte counter is restored, and
all retained history bits and every other state component are preserved. -/
theorem finishRecordCursor_spec (cap : ℕ) (src dummy : Fin (ns+1)) (SC OP : Fin nr)
    (hsd : src≠dummy) (hOS : OP≠SC) (records : List (List Bool)) (pre rest : List Bool)
    (hend : rest.headD false=false)
    (hne : ∀ record∈records,record≠[]) (σ : WState ns nr)
    (hs : σ.st src=pre++records.flatMap frame++rest)
    (hh : σ.sh src=pre.length) (hd : σ.sh dummy=(σ.st dummy).length)
    (ho : σ.val OP≤cap) (hSC : σ.val SC=0)
    (hcap : (records.flatMap frame).length≤cap) :
    WExec cap (finishRecordCursor src SC) σ
      (σ.seth src (pre.length+(records.flatMap frame).length)) (40*((records.flatMap frame).length+1)) := by
  have e1 := CounterAsm.frameLoop_spec cap hsd hOS
    (emits_none (cap:=cap) (dst:=dummy) (OP:=OP)) (d:=0) (by intro b;simp)
    rest hend records pre σ hne hs hh hd
    (by simpa using ho) (by rw [hSC];omega)
  have hz : (records.flatMap frame).flatMap (fun _=>([]:List Bool))=[] := by simp
  rw [hz] at e1
  let a := adv src dummy OP SC σ [] (records.flatMap frame).length
  have e2 := wclear_spec cap SC (records.flatMap frame).length a
    (by simp [a,adv,hSC]) (by simpa only [a,adv_val_SC,hSC,Nat.zero_add] using hcap)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi:i=src
    · subst i;simp [a,adv,appendO,hsd,hh,Nat.add_assoc]
    · simp [a,adv,appendO,Function.update_of_ne hi]
  · simp [a,adv,appendO]
  · funext i
    by_cases hi:i=SC
    · subst i;simp [a,adv,appendO,hOS.symm,hSC]
    · simp [a,adv,appendO,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageTuple
