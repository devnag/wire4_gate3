import Proof.Quartic.StagePrint.CutFieldScan
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.CutScan

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual row
stride is copied for each row, then the encoded fields are skipped
and the equality counter is incremented. -/
def countRow (src : Fin (ns+1)) (R : Fin 6 ↪ Fin nr) : WM ns nr :=
  .seq (wcopyR (R 2) (R 3) (R 4))
    (.seq (skipFields src (R 1) (R 3)) (.inc (R 5)))

/-- `lem:print` and `prop:time`, paper/paper.tex: one counted row preserves its stride and consumes
only the actual signed field encodings. -/
theorem countRow_spec (cap : ℕ) (src dst : Fin (ns+1)) (R : Fin 6 ↪ Fin nr)
    (hsd : src≠dst) (fields : List (List Bool)) (pre suffix : List Bool) (a : WState ns nr)
    (hsource : a.st src=pre++fields.flatMap frame++suffix) (hhead : a.sh src=pre.length)
    (hout : a.sh dst=(a.st dst).length) (hstride : a.val (R 2)=fields.length)
    (hK : a.val (R 3)=0) (hT : a.val (R 4)=0)
    (hOP : a.val (R 0)≤cap) (hsourceCap : a.val (R 1)+(fields.flatMap frame).length≤cap)
    (hcountCap : fields.length≤cap) (hEQCap : a.val (R 5)+1≤cap) :
    WExec cap (countRow src R) a
      ((adv src dst (R 0) (R 1) a [] (fields.flatMap frame).length).setv (R 5) (a.val (R 5)+1))
      (25*(fields.flatMap frame).length+22*fields.length+9) := by
  have ne : ∀ {i j : Fin 6},i≠j→R i≠R j := fun h=>R.injective.ne h
  have ec:=wcopyR_spec cap (R 2) (R 3) (R 4)
    (ne (by decide)) (ne (by decide)) (ne (by decide)) a hK hT (by rw [hstride];exact hcountCap)
  let b:=a.setv (R 3) fields.length
  have ec' : WExec cap (wcopyR (R 2) (R 3) (R 4)) a b (18*fields.length+3) := by
    simpa only [hstride] using ec
  have es:=skipFields_spec cap src dst (R 0) (R 1) (R 3) hsd
    (ne (by decide)) (ne (by decide)) (ne (by decide)) fields pre suffix b
    hsource hhead hout (by simp only [b,WState.setv_val,Function.update_self])
    (by simpa only [b,WState.setv_val,Function.update_of_ne (ne (show (0:Fin 6)≠3 by decide))] using hOP)
    (by simpa only [b,WState.setv_val,Function.update_of_ne (ne (show (1:Fin 6)≠3 by decide))] using hsourceCap)
    hcountCap
  let c:=adv src dst (R 0) (R 1) a [] (fields.flatMap frame).length
  have heq : (adv src dst (R 0) (R 1) b [] (fields.flatMap frame).length).setv (R 3) 0=c := by
    rw [show b=a.setv (R 3) fields.length from rfl,
      adv_setv _ _ _ (R 3) _ (ne (by decide)) (ne (by decide)),wsetv_setv]
    have hz : c.val (R 3)=0 := by
      rw [adv_val_other _ _ _ (R 3) (ne (by decide)) (ne (by decide)),hK]
    exact hz ▸ wsetv_same c (R 3)
  rw [heq] at es
  have hce : c.val (R 5)=a.val (R 5) :=
    adv_val_other _ _ _ (R 5) (ne (by decide)) (ne (by decide))
  have ei:=WExec.inc (cap:=cap) (R 5) c (by rw [hce];exact hEQCap)
  have whole:=WExec.seq ec' (WExec.seq es ei)
  refine WExec.cast cap whole ?_ ?_
  · rw [hce]
  · omega

end NearQuarticWires.StagePrint.CutScan
