import Proof.Quartic.StageNativeHeader.Call

/-!
# The call never touches the output

Paper: `lem:print`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control NearQuarticWires.StagePrint

theorem sbank_ne_out (j : Fin tc) : ¬ (13 + j.val = 1) := by omega

/-- **The call avoids the output.** -/
theorem call_avoids : WMX.Avoids sOUT (callAppendProgram site sY rOY) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [WMX.Avoids, WM.Avoids, callP, WMX.machZ, NearCubicGates.Close.WorkerArith.guardP,
      NearCubicGates.Close.WorkerArith.tallyP, NearCubicGates.Close.WorkerArith.twoOnes, BinW.width, BinW.widthW,
      BinW.widthLoop, BinW.backLoop, WM.rewind, WMX.wr, WMX.fwd, WMX.inc, WMX.dec, WMX.skip, Site.input, site,
      sbank, sTA, sGA, sL, sOUT, strm, Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬ v = 1)))
    all_goals first | omega | (intro j; simp [sbank]; omega) | simp
  · simp [WMX.Avoids, WM.Avoids, appendFrameReset, NearCubicGates.Close.CounterAsm.frameCopy,
      NearCubicGates.Close.Recovery.HTParts.pairLoop, NearCubicGates.Close.Recovery.HTParts.cellE, emitC, WM.fwdC,
      WM.rewind, site, sbank, sY, sOUT, strm, Fin.ext_iff]
    all_goals first | omega | simp
  · simp [WMX.Avoids, WM.Avoids, cleanP, eraseP, WMX.machZ, Site.swept, NearCubicGates.Close.WorkerArith.clearSelfP,
      WMX.wr, WMX.fwd, WMX.bwd, WMX.inc, WMX.dec, WMX.skip, WM.rewind, site, sbank, sTA, sGA, sL, sOUT, strm,
      Fin.ext_iff]
    all_goals (repeat' (first | apply And.intro | apply addCases_val (P := fun v => ¬ v = 1)))
    all_goals first | omega | (intro j; simp [sbank]; omega) | (intro h; cases h)

end NearQuarticWires.StageNativeHeader
