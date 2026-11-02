import Proof.Gates.Transfer.Symmetric
import Proof.Quartic.Statement.Budget
import Proof.Quartic.Statement.Joint

set_option autoImplicit false

namespace NearQuarticWires.GateCorollary

open NearCubicWires NearCubicGates.Target
open NearCubicGates.Close.Transfer
open NearQuarticWires.Statement

/-- `cor:gates`, paper/paper.tex: finite-cube
complementation preserves every original nonzero input coefficient. -/
theorem complement_support {n : ℕ} (g : RealThresholdGate n) :
    (complementGate g).support = g.support := rfl

/-- `cor:gates`, paper/paper.tex: positive copies
and complemented negative copies have total count equal to charged
integral top weight, including the empty circuit. -/
theorem replication_count {n : ℕ} (C : WeightedSymmetricCircuit n) :
    (toSymmetric C).bottomCount = C.topWeight := rfl

/-- `cor:gates`, paper/paper.tex: the fixed negative
copy offset in the symmetric lookup preserves the original Boolean
function exactly. -/
theorem replication_eval {n : ℕ} (C : WeightedSymmetricCircuit n) (x : BitInput n) :
    (toSymmetric C).eval x = C.eval x := toSymmetric_eval C x

/-- `cor:gates`, paper/paper.tex: each charged copy
costs its at most n original input wires and its one top wire. -/
theorem replication_wires {n : ℕ} (C : WeightedSymmetricCircuit n) :
    wires (toSymmetric C) ≤ (n + 1) * C.topWeight := by
  rw [wires_eq_wireCount, Nat.mul_comm]
  exact toSymmetric_wireCount C

/-- `cor:gates`, paper/paper.tex: each ordinary
bottom occurrence costs at most n original input wires and one top wire. -/
theorem occurrence_wires {n : ℕ} (C : SymmetricThresholdCircuit n) :
    wires C ≤ (n + 1) * C.bottomCount := by
  rw [wires_eq_wireCount]
  unfold SymmetricThresholdCircuit.wireCount
  calc
    ∑ i, ((C.bottom i).support.card + 1) ≤ ∑ _i : Fin C.bottomCount, (n + 1) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi := Finset.card_le_univ (C.bottom i).support
      simp only [Fintype.card_fin] at hi
      omega
    _ = (n + 1) * C.bottomCount := by simp [Nat.mul_comm]

/-- `cor:gates`, paper/paper.tex: exact replication
preserves agreement with every language at the original input length. -/
theorem replication_agreement {n : ℕ} (C : WeightedSymmetricCircuit n) (F : Language) :
    agr (toSymmetric C) F = NearCubicGates.Target.agreement C F := by
  simp only [agr, NearCubicGates.Target.agreement, toSymmetric_eval]

end NearQuarticWires.GateCorollary
