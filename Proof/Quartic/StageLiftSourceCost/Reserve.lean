import Proof.Quartic.StageLift.SourceBudget
import Proof.Quartic.StageCert.MomentSourcePrice
import Proof.Quartic.StageLiftMasks.Request

/-!
# Selected reserve for the actual source enumeration

`lem:print` and `prop:time`, paper/paper.tex: the original closed-walk census and all guarded mask
tuples fit the selected outer-column reserve, with the original
finite degree constant unchanged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftSourceCost
open NearCubicWires NearCubicGates.Close.Cells StageLift

variable {B1 B2 : ℕ}

theorem walkCount_pos (r : Greedy.PrintRequest B1 B2) :
    1 ≤ r.child.cellCall.seed.N^8 := by
  have hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  rw [StageLiftMasks.request_N r,hs.N_eq]
  exact Nat.pow_pos (Nat.pow_pos (by decide))

theorem walkCount_le (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N^8 ≤ 2^(4*r.child.selected.1.k) := by
  have hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  rw [StageLiftMasks.request_N r,hs.N_eq,←pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  have hh:=Nat.div_mul_le_self r.child.selected.1.k 2
  omega

theorem original_tuple_reserve (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N^8*(Builder.allGates r.child.call).length^r.child.selected.1.Xmax ≤ 
      2^(r.child.call.n-r.child.selected.1.k) := by
  let mr:=StageLiftMasks.maskMomentRequest r ⟨0,walkCount_pos r⟩
  have hh:=StageCert.Tokens.MomentRequest.source_tuple_reserve mr
  exact (Nat.mul_le_mul_right _ (walkCount_le r)).trans hh

theorem original_tuple_pos (r : Greedy.PrintRequest B1 B2) :
    1 ≤ (Builder.allGates r.child.call).length^r.child.selected.1.Xmax :=
  Nat.pow_pos (print_originalPool_pos r)

theorem walkCount_le_columns (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.seed.N^8 ≤ 2^(r.child.call.n-r.child.selected.1.k) :=
  (Nat.le_mul_of_pos_right _ (original_tuple_pos r)).trans (original_tuple_reserve r)

end NearQuarticWires.StageLiftSourceCost
