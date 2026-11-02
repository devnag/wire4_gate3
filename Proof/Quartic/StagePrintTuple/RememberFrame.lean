import Proof.Quartic.StagePrintTuple.PayloadCopy
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one actual
frame scan records its real byte count in a persistent register before
the cache cursor is reset for support selection. -/
def rememberFrameProgram (src : Fin (ns+1)) (SC LEN TMP : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (fun _=>WM.skip))
    (.seq (wcopyR SC LEN TMP) (WM.rewind src SC))

/-- `lem:print` and `prop:time`, paper/paper.tex: the full cache byte count is physically computed and
retained; the scan counter, temporary register and source cursor are
restored. No source-length field or callee-output observation is used. -/
theorem rememberFrameProgram_spec (cap : ℕ) (src dummy : Fin (ns+1)) (SC LEN TMP OP : Fin nr)
    (hsd : src≠dummy) (hOS : OP≠SC) (hSL : SC≠LEN) (hST : SC≠TMP) (hLT : LEN≠TMP)
    (bits : List Bool) (σ : WState ns nr) (hs : σ.st src=frame bits) (hh : σ.sh src=0)
    (hd : σ.sh dummy=(σ.st dummy).length) (ho : σ.val OP≤cap)
    (hSC : σ.val SC=0) (hLEN : σ.val LEN=0) (hTMP : σ.val TMP=0)
    (hcap : (frame bits).length≤cap) :
    WExec cap (rememberFrameProgram src SC LEN TMP) σ (σ.setv LEN (frame bits).length)
      (60*((frame bits).length+1)) := by
  have e1 := CounterAsm.frameCopy_spec cap hsd hOS
    (emits_none (cap:=cap) (dst:=dummy) (OP:=OP)) (d:=0) (by intro b;simp)
    bits [] [] σ (by simpa using hs) (by simpa using hh) hd
    (by simpa using ho) (by rw [hSC];omega)
  have hz : (frame bits).flatMap (fun _=>([]:List Bool))=[] := by simp
  rw [hz] at e1
  let a := adv src dummy OP SC σ [] (frame bits).length
  have e2 := wcopyR_spec cap SC LEN TMP hSL hST hLT a
    (by simp [a,adv,appendO,hSL.symm,hLEN])
    (by simp [a,adv,appendO,hST.symm,hTMP]) (by simpa only [a,adv_val_SC,hSC,Nat.zero_add] using hcap)
  let b := a.setv LEN (frame bits).length
  have e2' : WExec cap (wcopyR SC LEN TMP) a b (18*(frame bits).length+3) := by
    simpa [b,a,adv,hSC] using e2
  have e3 := wrewind_spec cap src SC (frame bits).length b
    (by simp [b,a,adv,hSC,hSL]) (by simpa only [b,WState.setv_val,Function.update_of_ne hSL,a,adv_val_SC,hSC,Nat.zero_add] using hcap)
  refine (e1.seq (e2'.seq e3)).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi:i=src
    · subst i;simp [b,a,adv,appendO,hh]
    · simp [b,a,adv,appendO,Function.update_of_ne hi]
  · simp [b,a,adv,appendO]
  · funext i
    by_cases hi:i=SC
    · subst i;simp [b,a,adv,appendO,hSL,hOS.symm,hSC]
    · by_cases hiL:i=LEN
      · subst i;simp [b,a,adv,appendO,hSL.symm]
      · simp [b,a,adv,appendO,Function.update_of_ne hi,Function.update_of_ne hiL]
  · rfl

end NearQuarticWires.StageTuple
