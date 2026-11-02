import Proof.Quartic.Worker.Prelude
import Proof.Gates.Codec.Copy
import Proof.Gates.Codec.Circuit
import Proof.Quartic.Worker.Codec.ParityW
import Proof.Gates.Interfaces.Counter

/-!
# WorkerArith.FitSpec for the weak machine of the wire measure

Definitions: `CircuitSizeFit`, `RowSizeFit`.

Adapted from `Proof.Gates.WorkerArith.FitSpec` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4`
(`NearQuarticWires.Worker4.Counter`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.WorkerArith.WorkerBounds
open NearCubicGates NearCubicGates.Close

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close

def CircuitSizeFit : Prop :=
  ∀ (q : ℕ) (C : Interfaces.NCircuit q) (W : ℕ), (Interfaces.circuitWord C).length + q + 2 ≤ W →
    Codec.CircuitFits (4 * W + 4) C ∧ Codec.circuitCost C ≤ 100000 * W ^ 3 ∧
      Codec.copyCircuitCost C ≤ 100000 * W ^ 3 ∧ ∀ cap V : ℕ, V + 20 * W + 20 ≤ cap → Codec.CopyFits cap V C

def RowSizeFit : Prop :=
  ∀ (q : ℕ) (row : List ℕ) (W : ℕ), (∀ x ∈ row, x < q) → row.length ≤ q → q + 2 ≤ W →
    Codec.rowCost row ≤ 100000 * W ^ 3 ∧
      (2 ^ (natBitLength row.length + 1) ≤ 4 * W + 4 ∧ row.length ≤ 4 * W + 4 ∧
        ∀ x ∈ row, natBitLength x + 1 ≤ 4 * W + 4) ∧
      (Interfaces.listWord natWord row).length ≤ 10 * W ^ 2

end NearQuarticWires.Worker4.WorkerArith.WorkerBounds
