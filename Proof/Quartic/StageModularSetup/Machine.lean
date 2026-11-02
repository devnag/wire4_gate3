import Proof.Quartic.StageModularSetup.Loaded

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageModularCuts StageModularCuts.Setup

/-- `lem:print`, paper/paper.tex: the cold
setup uses the paid actual eleven-field loader, then initializes the
complete bounded binary arithmetic state from its literal source bytes. -/
noncomputable def setup : StageModularCuts.Program :=
  .seq (.mach Top.loadM loadMap) initializeLoaded

/-- `lem:print` and `prop:time`, paper/paper.tex: ordinary cold setup reaches the exact downstream ready
state within the frozen linear-source capacity and physical clock. -/
theorem setup_spec : SetupSpec setup := by
  intro r
  have eLoad:=load_spec (capacity r) r
  have eReady:=initializeLoaded_spec r
  have hclock:=setup_initialization_clock r
  refine (eLoad.seq eReady).cast (capacity r) rfl ?_
  unfold clock
  omega

end NearQuarticWires.StageModularSetup
