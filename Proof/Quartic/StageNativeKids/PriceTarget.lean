import Proof.Quartic.StageNativeKids.Selection
import Proof.Quartic.StageNativeKids.RoleBounds

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open StageTuple StagePrint

/-- `imp:disjoint` and `prop:time`, paper/paper.tex: the structural original-source price retains
the actual sharp original-child cap as a separate resource, without
assuming that it has already been eliminated in terms of arity. -/
def NativeKidsRequest.originalSourceScale (r : NativeKidsRequest) : ℕ :=
  r.word.length + r.header.call.n + Cells.childCap r.header.call.n (Call.B0 r.header.call.n) + 1

/-- `lem:print`, paper/paper.tex: an actual
original formula atom can exist only at positive original dimension,
by the original quartic occurrence census. -/
theorem NativeKidsRequest.dimension_pos (r : NativeKidsRequest) : 0 < r.header.call.n := by
  have hG := original_count_bound r.toRowContext
  have hi := r.atom.isLt
  by_contra hn
  have hn0 : r.header.call.n = 0 := by omega
  have hG0 : (Builder.allGates r.header.call).length ≤ 0 := by
    calc
      _ ≤ 2 * r.header.call.n ^ 4 := hG
      _ = 0 := by rw [hn0]; norm_num
  omega

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: every actual source atom's complete original
child loop is bounded by the unchanged original sharp child cap. -/
theorem NativeKidsRequest.originalKids_cap (r : NativeKidsRequest) :
    (r.toRowContext.nativeKids r.atom).length ≤
      Cells.childCap r.header.call.n (Call.B0 r.header.call.n) :=
  r.toRowContext.nativeKids_length_le r.atom r.dimension_pos

/-- `prop:time`, paper/paper.tex: the
four actual original-source leaf clocks have one structural polynomial
envelope. This predicate refers only to the concrete source-selected
counter and every concrete original pipeline row, with the real child
cap retained and no degree or numeric walk/radix parameter. -/
def OriginalSourcePrice (K e : ℕ) : Prop :=
  ∀ r : NativeKidsRequest,
    (∀ h : (r.toRowContext.originalIndex r.atom).val < r.header.call.first.gates.length,
      indexedOriginalCountBudget (firstCountSource r h) ≤ K * r.originalSourceScale ^ e) ∧
    (∀ h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val,
      indexedOriginalCountBudget (secondCountSource r h) ≤ K * r.originalSourceScale ^ e) ∧
    (∀ (h : (r.toRowContext.originalIndex r.atom).val < r.header.call.first.gates.length)
      (j : Fin (exactChildren (callAtoms r.header.call (r.toRowContext.originalIndex r.atom))).length),
      (r.toRowContext.firstPipeline r.atom h j).budget ≤ K * r.originalSourceScale ^ e) ∧
    (∀ (h : r.header.call.first.gates.length ≤ (r.toRowContext.originalIndex r.atom).val)
      (j : Fin (exactChildren (callAtoms r.header.call (r.toRowContext.originalIndex r.atom))).length),
      (r.toRowContext.secondPipeline r.atom h j).budget ≤ K * r.originalSourceScale ^ e)

end NearQuarticWires.StageNativeKids
