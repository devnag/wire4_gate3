import Proof.Quartic.StageModularCuts.SetupLoad
import Proof.Wire_3_5.PrimAsmEmit

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open StageModularCuts

/-- `lem:print`, paper/paper.tex: convert the
actual unary affine dimension into its retained coefficient-field stride. -/
def doubleStride : WM 15 16 :=
  .seq (wcopyR 8 9 10) (.seq (WM.move 9 8) (.inc 8))

/-- `prop:time`, paper/paper.tex: the stride
is physically computed from the small dimension, preserving all other data. -/
theorem doubleStride_spec (cap value : ℕ) (a : State)
    (h8 : a.val 8=value) (h9 : a.val 9=0) (h10 : a.val 10=0)
    (hcap : 2*value+1≤cap) :
    WExec cap doubleStride a (a.setv 8 (2*value+1)) (30*value+20) := by
  have eCopy:=wcopyR_spec cap (8 : Fin 16) 9 10 (by decide) (by decide) (by decide)
    a h9 h10 (by rw [h8];omega)
  rw [h8] at eCopy
  let b:=a.setv 9 value
  have eMove:=wmove_spec cap (9 : Fin 16) 8 (by decide) value b
    (by simp [b]) (by simp [b];omega) (by simp [b,h8];omega)
  let c:=(b.setv 9 0).setv 8 (b.val 8+b.val 9)
  have hc8 : c.val 8=2*value := by simp [c,b,h8];omega
  have eInc:=WExec.inc (cap:=cap) (8 : Fin 16) c (by rw [hc8];omega)
  refine (eCopy.seq (eMove.seq eInc)).cast cap ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext reg
    by_cases hreg : reg=8
    · subst reg;simp [c,b,h8]
      omega
    · by_cases hreg9 : reg=9
      · subst reg;simp [c,b,h9]
      · simp [c,b,hreg,hreg9]
  · rfl

end NearQuarticWires.StageModularSetup
