import Proof.Quartic.StagePrep.ClosedDock
import Proof.Gates.Dispatch.Main

/-!
# The original-call polynomial cost of the zero-wire exit

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)

/-- The parity-list work of `sec:params`, paper/paper.tex, is bounded by the original explicit call word,
even when the original arity is very large. -/
theorem parity_length_le_callWord (c : Call) : c.parity.length ≤ (callWord c).length := by
  have hflat := length_le_flatMap c.parity natWord (fun x => by rw [natWord_length]; omega)
  have hword := congrArg List.length (callWord_eq c)
  simp only [listWord, List.length_append] at hword
  omega

/-- The actual zero-wire exit budget of `prop:time`,
paper/paper.tex, does not depend on witness length. -/
def closedOutputCost (K : ℕ) (c : Call) (_ : List Bool) : ℕ :=
  oddCostT (callWord c).length c.parity.length (wdOf K (callWord c).length) +
    2 * closedZeroWordLen + 50

/-- The actual zero-wire exit budget of `prop:time`,
paper/paper.tex, is polynomial in the original
call word rather than in its possibly much larger arity. -/
theorem closedOutputCost_poly (K : ℕ) : Program.PolyCost (closedOutputCost K) := by
  have hp : PolyB (fun L => oddCostT L L (wdOf K L) + 2 * closedZeroWordLen + 50) := by
    unfold oddCostT oddCost wdOf
    polyb
  obtain ⟨C, e, hCe⟩ := hp
  refine ⟨C, e, ?_⟩
  intro c w
  have hlen := parity_length_le_callWord c
  have hm : oddCostT (callWord c).length c.parity.length (wdOf K (callWord c).length) ≤
      oddCostT (callWord c).length (callWord c).length (wdOf K (callWord c).length) := by
    unfold oddCostT oddCost
    gcongr
  exact (Nat.add_le_add_right (Nat.add_le_add_right hm _) _).trans (hCe _)

end NearQuarticWires.StagePrep
