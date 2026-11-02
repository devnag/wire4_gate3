import Proof.Quartic.StageModularSetup.Widths
import Proof.Wire_3_5.CompilerMachinePoolConv

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageModularCuts StageModularCuts.Setup

/-- `lem:print`, paper/paper.tex: the additional
work bit fits the actual binary modulus even at the inclusive endpoint. -/
theorem modulus_length_bound (r : Request) : natBitLength r.modulus≤r.fieldWidth+1 := by
  apply Pool.natBitLength_le _ _ (by omega)
  have hp : 0<2^r.fieldWidth := pow_pos (by decide) _
  have hq:=r.modulus_fit
  rw [pow_succ]
  omega

/-- `prop:time`, paper/paper.tex: the frozen
capacity contains every width, source cursor, and work-word counter used
by the actual binary setup, with no dependence on numeric magnitudes. -/
theorem setup_counter_capacity (r : Request) : 100*(scale r+1)≤ capacity r := by
  have hs : 2≤ scale r := by unfold scale;omega
  have hp : scale r≤(scale r)^8 := Nat.le_self_pow (by decide) _
  have hm : 10^8*(scale r)^8≤ capacity r := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- `prop:time`, paper/paper.tex: the loaded
binary initialization and all sequencer steps fit the fixed setup clock. -/
theorem setup_initialization_clock (r : Request) :
    100*(r.width+r.fieldWidth+1)+500*(r.fieldWidth+2)+
      5*(60*(r.fieldWidth+1)+41)+3≤10^6*(scale r)^4 := by
  have hs : 2≤ scale r := by unfold scale;omega
  have hp : scale r≤(scale r)^4 := Nat.le_self_pow (by decide) _
  have hw : r.width+r.fieldWidth+2≤ scale r := by unfold scale;omega
  omega

end NearQuarticWires.StageModularSetup
