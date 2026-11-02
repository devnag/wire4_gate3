import Proof.Quartic.StageModularSetup.Stride
import Proof.Quartic.StagePrint.UnaryRegister

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StageModularCuts StageModularCuts.Setup

/-- `lem:print`, paper/paper.tex: read the two
actual unary dimensions, return both source heads, and compute the
extra binary work bit and affine-field stride. -/
def initializeWidths : StageModularCuts.Program :=
  .seq (StagePrint.unaryRegister 4 0 7)
    (.seq (WMX.inc 7) (.seq (StagePrint.unaryRegister 5 0 8) (.wm doubleStride)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the retained widths come only from the loaded literal
source; no modulus value or row coefficient enters a unary counter. -/
theorem initializeWidths_spec (cap : ℕ) (r : Request)
    (hcap : 2*r.width+2*r.fieldWidth+10≤cap) :
    WXExec cap initializeWidths (loaded r)
      (((loaded r).setv 7 (r.fieldWidth+1)).setv 8 (2*r.width+1))
      (100*(r.width+r.fieldWidth+1)) := by
  have eP:=StagePrint.unaryRegister_spec cap (4 : Fin 16) (0 : Fin 16) 7 (by decide)
    (loaded r) r.fieldWidth rfl rfl rfl rfl (by omega)
  let b:=(loaded r).setv 7 r.fieldWidth
  have eInc:=WXExec.inc cap (7 : Fin 16) b (by simp [b];omega)
  let c:=b.setv 7 (b.val 7+1)
  have eD:=StagePrint.unaryRegister_spec cap (5 : Fin 16) (0 : Fin 16) 8 (by decide)
    c r.width (by simp [c,b];rfl) (by simp [c,b];rfl) (by simp [c,b];rfl) (by simp [c,b];rfl)
    (by omega)
  let d:=c.setv 8 r.width
  have eStride:=doubleStride_spec cap r.width d (by simp [d])
    (by simp [d,c,b,loaded]) (by simp [d,c,b,loaded]) (by omega)
  refine (eP.seq (eInc.seq (eD.seq (WXExec.wm eStride)))).cast cap ?_ (by omega)
  simp only [d,c,b,WState.setv_val,Function.update_self,wsetv_setv]

end NearQuarticWires.StageModularSetup
