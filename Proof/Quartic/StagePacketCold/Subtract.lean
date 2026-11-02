import Proof.Quartic.StagePacketCold.Acquire

set_option autoImplicit false

namespace NearQuarticWires.StagePacketCold

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: subtract the
physically counted skipped bytes from the measured finite source size. -/
def subtractConsumed (used remaining : Fin nr) : WM ns nr :=
  .whr used (.seq (.dec used) (.dec remaining))

/-- `prop:time`, paper/paper.tex: subtraction
uses one paid decrement for each actual skipped source byte. -/
theorem subtractConsumed_spec (cap : ℕ) (used remaining : Fin nr) (hne : used≠remaining) :
    ∀ (count : ℕ) (a : WState ns nr),a.val used=count→count≤a.val remaining→a.val remaining≤cap→
      WExec cap (subtractConsumed used remaining) a
        ((a.setv used 0).setv remaining (a.val remaining-count)) (5*count+1)
  | 0,a,hused,_,_=>by
      have hstate : (a.setv used 0).setv remaining (a.val remaining-0)=a := by
        rw [Nat.sub_zero,wsetv_comm _ _ _ hne,wsetv_same,←hused,wsetv_same]
      rw [hstate]
      exact WExec.whrF hused
  | count+1,a,hused,hcount,hcap=>by
      have eUsed:=WExec.dec (cap:=cap) used a (by omega)
      let b:=a.setv used (a.val used-1)
      have hbRemaining : b.val remaining=a.val remaining := by simp [b,Function.update_of_ne hne.symm]
      have eRemaining:=WExec.dec (cap:=cap) remaining b (by rw [hbRemaining];exact hcap)
      let c:=b.setv remaining (b.val remaining-1)
      have hcUsed : c.val used=count := by simp [c,b,Function.update_of_ne hne,hused]
      have hcRemaining : c.val remaining=a.val remaining-1 := by simp [c,hbRemaining]
      have eRest:=subtractConsumed_spec cap used remaining hne count c hcUsed
        (by rw [hcRemaining];omega) (by rw [hcRemaining];omega)
      refine (WExec.whrT (by omega) (eUsed.seq eRemaining) eRest).cast cap ?_ (by omega)
      apply WState.eq
      · rfl
      · rfl
      · funext reg
        by_cases hu : reg=used
        · subst reg
          simp [c,b,hne,hne.symm]
        · by_cases hr : reg=remaining
          · subst reg
            simp [c,b,hne.symm]
            omega
          · simp [c,b,Function.update_apply,hu,hr]
      · rfl

end NearQuarticWires.StagePacketCold
