import Proof.Quartic.StageModularSetup.Machine
import Proof.Quartic.StageModularCuts.Assembly

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

/-- `lem:print` and `prop:time`, paper/paper.tex: the concrete cold setup and actual sequential signed-cut
reducer yield the complete modular printer with its frozen output and budget. -/
noncomputable def modularCutsPrinter : StagePrint.Downstream.ModularCutsPrinter :=
  StageModularCuts.modularCutsPrinter_of_setup setup setup_spec

end NearQuarticWires.StageModularSetup
