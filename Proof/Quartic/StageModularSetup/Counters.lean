import Proof.Quartic.StageModularSetup.ReadLength
import Proof.Quartic.StagePacketCold.Subtract

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open StageModularCuts

/-- `lem:print`, paper/paper.tex: prepare the
actual binary-tail copy length and zero-padding count from the retained
width and the physically parsed modulus bit length. -/
def prepareCounters : WM 15 16 :=
  .seq (wcopyR 0 3 4) (.seq (wcopyR 7 9 10) (StagePacketCold.subtractConsumed 0 9))

/-- `lem:print` and `prop:time`, paper/paper.tex: all copy and padding counts are computed by paid
bounded instructions and every temporary counter is restored. -/
theorem prepareCounters_spec (cap width len : ℕ) (a : State)
    (h0 : a.val 0=len) (h7 : a.val 7=width)
    (h3 : a.val 3=0) (h4 : a.val 4=0) (h9 : a.val 9=0) (h10 : a.val 10=0)
    (hlen : len≤width) (hcap : width≤cap) :
    WExec cap prepareCounters a (((a.setv 3 len).setv 9 (width-len)).setv 0 0)
      (100*(width+1)) := by
  have eL:=wcopyR_spec cap (0 : Fin 16) 3 4 (by decide) (by decide) (by decide) a h3 h4 (by rw [h0];omega)
  rw [h0] at eL
  let b:=a.setv 3 len
  have hb7 : b.val 7=width := by simp [b,h7]
  have eW:=wcopyR_spec cap (7 : Fin 16) 9 10 (by decide) (by decide) (by decide) b
    (by simp [b,h9]) (by simp [b,h10]) (by rw [hb7];exact hcap)
  rw [hb7] at eW
  let c:=b.setv 9 width
  have eSub:=StagePacketCold.subtractConsumed_spec cap (0 : Fin 16) 9 (by decide) len c
    (by simp [c,b,h0]) (by simp [c];exact hlen) (by simp [c];exact hcap)
  refine (eL.seq (eW.seq eSub)).cast cap ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext reg
    by_cases hreg : reg=0
    · subst reg;simp [c,b]
    · by_cases hreg9 : reg=9
      · subst reg;simp [c,b]
      · simp [c,b,Function.update_apply,hreg,hreg9]
  · rfl

end NearQuarticWires.StageModularSetup
