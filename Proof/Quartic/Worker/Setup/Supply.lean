import Proof.Quartic.Worker.Prelude
import Proof.Quartic.Worker.Setup.Uniform
import Proof.Gates.OuterM.Width
import Proof.Gates.OuterM.ARun
import Proof.Quartic.Worker.Setup.CompU

/-!
# Setup.Supply for the weak machine of the wire measure

Main statements: `setupSupply_of`, `setupSupply_of_subst`.

Adapted from `Proof.Gates.Setup.Supply` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4`
(`NearQuarticWires.Worker4.Counter`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.Setup
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.Setup

open NearCubicGates.Close NearCubicGates.Close.Transfer
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget

theorem setupSupply_of (hC : ∀ (s : GateSources) (P : ThreeQueryPCPP), CompU s P) : SetupSupply :=
  fun s P => setupU_of s P (hC s P) (fun g => OuterM.widthDonor s.mw (g.sv s)) (fun g => OuterM.aRun s.mw (g.sv s))

theorem setupSupply_of_subst (h : Succinct.SubstMachine.SubstReadySpec) : SetupSupply :=
  setupSupply_of (fun s P => compU_of h s P)

end NearQuarticWires.Worker4.Setup
