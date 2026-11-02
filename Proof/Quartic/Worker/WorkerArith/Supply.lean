import Proof.Quartic.Worker.Prelude
import Proof.Quartic.Worker.WorkerArith.Rest
import Proof.Quartic.Worker.WorkerArith.Fit

/-!
# WorkerArith.Supply for the weak machine of the wire measure

* `workerSupply_of_fit`: **The worker supply**, from the per-circuit and per-row size facts.

Adapted from `Proof.Gates.WorkerArith.Supply` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4`
(`NearQuarticWires.Worker4.Counter`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.WorkerArith
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.WorkerArith

/-- **The worker supply**, from the per-circuit and per-row size facts. -/
theorem workerSupply_of_fit (hCF : WorkerBounds.CircuitSizeFit) (hRF : WorkerBounds.RowSizeFit) (hSU : Setup.SetupSupply) :
    Closure.WorkerSupply :=
  workerSupply_of (hrest_of hCF hRF hSU)

theorem workerSupply (hSU : Setup.SetupSupply) : Closure.WorkerSupply :=
  workerSupply_of_fit WorkerBounds.circuitSizeFit WorkerBounds.rowSizeFit hSU

end NearQuarticWires.Worker4.WorkerArith
