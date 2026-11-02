import Proof.Quartic.StageGamma.Unframe
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Expand.PolyTab

/-- Step 3, `sec:algorithm`, paper/paper.tex: the actual outer
source is unframed once onto a separate raw streaming tape. -/
def acquireCarrier : WM 3 16 := StageGamma.unframeRecord 0 1 0

/-- Step 3 and `prop:time`, paper/paper.tex: one linear source acquisition leaves the real raw
source at head zero, with every scratch register blank. -/
theorem acquireCarrier_spec (bits : List Bool) (cap : ℕ) (hc : bits.length≤cap) :
    WExec cap acquireCarrier (idealStart 3 16 bits (fun _=>0))
      ((((idealStart 3 16 bits (fun _=>0)).sets 1 bits).seth 0 (2*bits.length+1)))
      (23*bits.length+5) := by
  simpa [acquireCarrier,idealStart] using StageGamma.unframeRecord_run cap (0 : Fin 4) 1 (by decide) (0 : Fin 16)
    bits [] [] (idealStart 3 16 bits (fun _=>0))
    (by simp [idealStart]) rfl rfl rfl hc

end NearQuarticWires.StageCompiledTerms
