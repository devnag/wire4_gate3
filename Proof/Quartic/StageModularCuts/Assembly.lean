import Proof.Quartic.StageModularCuts.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print` and `prop:time`, paper/paper.tex: composing an actual cold binary setup with the proved row
stream yields the literal framed modular-cut printer at its stated budget. -/
noncomputable def modularCutsPrinter_of_setup (setup : Program) (hsetup : Setup.SetupSpec setup) :
    StagePrint.Downstream.ModularCutsPrinter :=
  wordFunction_of_ideal (.seq setup streamProgram) (14 : Fin 16) (by decide)
    Setup.capacity Setup.lens (fun r => Setup.clock r + 1 + streamCost r)
    full_clock_bound (fun r => by
      obtain ⟨b, hb, hout⟩ := streamProgram_spec r
      exact ⟨rfl, b, WXExec.seq (hsetup r) hb, hout⟩)

end NearQuarticWires.StageModularCuts
