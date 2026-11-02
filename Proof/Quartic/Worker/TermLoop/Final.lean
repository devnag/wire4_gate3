import Proof.Quartic.Worker.Prelude
import Proof.Quartic.Worker.TermLoop.Main
import Proof.Quartic.Worker.TermLoop.Exit
import Proof.Quartic.Worker.TermLoop.Gadget7

/-!
# TermLoop.Final for the weak machine of the wire measure

Main statements: `termLoop_ideal`, `w3d`.

Adapted from `Proof.Gates.TermLoop.Final` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4`
(`NearQuarticWires.Worker4.Counter`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.TermLoop
open NearCubicGates NearCubicGates.Close

open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Setup NearQuarticWires.Worker4.Setup

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams} (D : SetupData s P g)
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) (hct : ctr.program.program.tapeCount = D.tc) (ω : ℚ)

theorem termLoop_ideal : TermLoopIdeal D ctr hct ω := termLoop_ideal_of D ctr hct ω (gadget_ideal D ctr hct ω)

theorem w3d (hD : Counter.DenOK ctr) : TermLoopIdeal D ctr hct ω ∧ LoopExitVI D ctr ω hD :=
  ⟨termLoop_ideal D ctr hct ω, loopExit_vi D ctr ω hD⟩

end NearQuarticWires.Worker4.TermLoop
