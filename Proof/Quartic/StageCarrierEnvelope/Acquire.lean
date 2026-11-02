import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.CounterAsm.Copy
import Proof.Quartic.StagePacketCold.Acquire

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: measure
and copy the actual source frame once, retaining its physical byte
count and restoring both original and raw source heads to zero. -/
def acquireCarrier (src dst : Fin (ns+1)) (OP LEN TMP : Fin nr) : WM ns nr :=
  .seq (.whs src (StageGamma.unframePair src dst OP))
    (.seq (wcopyR OP LEN TMP) (.seq (WM.rewind dst OP)
      (.seq (wcopyR LEN OP TMP) (.seq (WM.rewind src OP)
        (.seq (wcopyR LEN OP TMP) (WM.rewind src OP))))))

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual source bit, measured count transfer,
and head return is paid linearly, with unrelated callee tapes preserved. -/
theorem acquireCarrier_run (cap : ℕ) (src dst : Fin (ns+1)) (OP LEN TMP : Fin nr)
    (hsd : src≠dst) (hOL : OP≠LEN) (hOT : OP≠TMP) (hLT : LEN≠TMP)
    (bits : List Bool) (a : WState ns nr)
    (hsource : a.st src=frame bits) (hhead : a.sh src=0)
    (hout : a.st dst=[]) (hohead : a.sh dst=0)
    (hOP : a.val OP=0) (hLEN : a.val LEN=0) (hTMP : a.val TMP=0)
    (hcap : 2*bits.length+4≤cap) :
    WExec cap (acquireCarrier src dst OP LEN TMP) a
      ((a.sets dst bits).setv LEN bits.length) (200*(bits.length+1)) := by
  have e1:=StageGamma.unframe_loop cap src dst hsd OP [] bits [] a
    (by simpa only [List.nil_append,List.append_nil] using hsource) hhead
    (by rw [hout,hohead];rfl) (by rw [hOP];omega)
  simp only [List.length_nil,Nat.zero_add] at e1
  let b:=(appendO a dst OP bits).seth src (2*bits.length)
  have hbOP : b.val OP=bits.length := by simp [b,hOP]
  have hbLEN : b.val LEN=0 := by simp [b,appendO,Function.update_of_ne hOL.symm,hLEN]
  have hbTMP : b.val TMP=0 := by simp [b,appendO,Function.update_of_ne hOT.symm,hTMP]
  have e2:=wcopyR_spec cap OP LEN TMP hOL hOT hLT b hbLEN hbTMP (by rw [hbOP];omega)
  rw [hbOP] at e2
  let c:=b.setv LEN bits.length
  have hcOP : c.val OP=bits.length := by simp [c,Function.update_of_ne hOL,hbOP]
  have e3:=wrewind_spec cap dst OP bits.length c hcOP (by rw [hcOP];omega)
  let d:=(c.setv OP 0).seth dst (c.sh dst-bits.length)
  have hdLEN : d.val LEN=bits.length := by simp [d,c,Function.update_of_ne hOL.symm]
  have hdTMP : d.val TMP=0 := by simp [d,c,Function.update_of_ne hOT.symm,Function.update_of_ne hLT.symm,hbTMP]
  have e4:=wcopyR_spec cap LEN OP TMP hOL.symm hLT hOT d (by simp [d]) hdTMP (by rw [hdLEN];omega)
  rw [hdLEN] at e4
  let e:=d.setv OP bits.length
  have e5:=wrewind_spec cap src OP bits.length e (by simp [e]) (by simp [e];omega)
  let f:=(e.setv OP 0).seth src (e.sh src-bits.length)
  have hfLEN : f.val LEN=bits.length := by simp [f,e,Function.update_of_ne hOL.symm,hdLEN]
  have hfTMP : f.val TMP=0 := by simp [f,e,Function.update_of_ne hOT.symm,hdTMP]
  have e6:=wcopyR_spec cap LEN OP TMP hOL.symm hLT hOT f (by simp [f]) hfTMP (by rw [hfLEN];omega)
  rw [hfLEN] at e6
  let g:=f.setv OP bits.length
  have e7:=wrewind_spec cap src OP bits.length g (by simp [g]) (by simp [g];omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))).cast cap ?_ (by omega)
  apply WState.eq
  · funext stream
    by_cases hs : stream=src
    · subst stream
      simp [g,f,e,d,c,b,appendO,hhead,hsd]
      omega
    · by_cases hd : stream=dst
      · subst stream
        simp [g,f,e,d,c,b,appendO,hohead,hsd.symm]
      · simp [g,f,e,d,c,b,appendO,hs,hd]
  · funext stream
    by_cases hd : stream=dst
    · subst stream
      simp [g,f,e,d,c,b,appendO,hout]
    · simp [g,f,e,d,c,b,appendO,hd]
  · funext reg
    by_cases ho : reg=OP
    · subst reg
      simp [g,f,e,d,c,b,appendO,Function.update_of_ne hOL,hOP]
    · by_cases hl : reg=LEN
      · subst reg
        simp [g,f,e,d,c,b,appendO,Function.update_of_ne hOL.symm]
      · simp [g,f,e,d,c,b,appendO,ho,hl]
  · rfl

end NearQuarticWires.StageCarrierEnvelope
