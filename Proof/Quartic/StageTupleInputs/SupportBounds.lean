import Proof.Quartic.StageTupleInputs.CounterHeader
import Proof.Quartic.StageTupleInputs.SupportLayout

set_option autoImplicit false

namespace NearQuarticWires.StageTupleInputs

/-- `prop:time`, paper/paper.tex: the actual
support-counter writer is paid quadratically by the existing small
support magnitude, including copies and scratch clearing. -/
theorem counterHeaderCost_bound (v V : ℕ) (hv : v+1≤V) (hV : 20≤V) :
    counterHeaderCost v≤1000*V^2 := by
  have hb:=bitLength_le v
  have h1 : NearCubicWires.natBitLength v+10≤2*V := by omega
  have h2 : 100*v+200≤200*V := by omega
  have hp:=Nat.mul_le_mul h1 h2
  unfold counterHeaderCost
  nlinarith only [hp,hv,hV]

end NearQuarticWires.StageTupleInputs
