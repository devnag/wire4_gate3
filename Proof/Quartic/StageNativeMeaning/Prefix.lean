import Proof.Quartic.StageNativeMeaning.Terms
import Proof.Quartic.StageNativeMeaning.Atoms

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Tabulator
open StagePrint StagePrint.NativeMeaning

def entryValue (r : StageTuple.TermCutRequest) (row column : ℕ) : ℤ :=
  ((nativeEqualityCuts r).map (fun c => EquationRow.exactValue c
    (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
    (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum

noncomputable def originalCenterValue (r : StageTuple.TermCutRequest) (z : ℕ) : ℤ :=
  Terms.eval (Cells.walkAtomPoint r.header.prepared.starParams (by decide : 0<4)
    (callPatterns r.header.call r.header.prepared
      (indexedWalk r.header.prepared.seedParameters.N r.walkCode)) (callAtoms r.header.call)
    (Builder.centerOf r.header.call r.header.prepared
      (Builder.translation r.header.call r.header.prepared r.header.witness) z)) r.terms

/-- `imp:partition` and `lem:print`, paper/paper.tex: the transposed native row-major ordinal is exactly the
actual original Builder center ordinal, with the low bits first. -/
theorem centerOf_major (r : StageTuple.RowContext) (high : ℕ)
    (low : Fin (2^PrimT.C4Geo.dRow r.header.prepared.starParams)) :
    Builder.centerOf r.header.call r.header.prepared
      (Builder.translation r.header.call r.header.prepared r.header.witness)
      (low.val + 2^PrimT.C4Geo.dRow r.header.prepared.starParams * high) =
      PrimT.C4Geo.centerAt r.header.prepared.starParams
        (Builder.translation r.header.call r.header.prepared r.header.witness) low.val high := by
  unfold Builder.centerOf
  have hp : 0 < 2^PrimT.C4Geo.dRow r.header.prepared.starParams := Nat.two_pow_pos _
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low.isLt,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt low.isLt, zero_add]

/-- `imp:partition`, paper/paper.tex: the complete
valid native rectangle has the exact original center count. -/
theorem nativePrefix_count (r : StageTuple.RowContext) :
    2^PrimT.C4Geo.dRow r.header.prepared.starParams * 2^PrimT.C4Geo.dR r.header.prepared.starParams =
      2^(r.header.call.n-r.header.parameters.k) := by
  rw [← pow_add, ← Builder.centerCount_eq r.header.call r.header.prepared]

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: the valid row-major prefix of
the ACTUAL custom-Phi native equality values is the original Builder
center sequence, without a good-column assumption or a permutation. -/
theorem native_value_prefix (r : StageTuple.TermCutRequest) :
    let U := 2^PrimT.C4Geo.dRow r.header.prepared.starParams
    let C := 2^PrimT.C4Geo.dR r.header.prepared.starParams
    (pvals false (fun high low : Fin U => entryValue r high.val low.val)).take (U*C) =
      List.ofFn (fun z : Fin (U*C) => originalCenterValue r z.val) := by
  dsimp only
  have hC : 2^PrimT.C4Geo.dR r.header.prepared.starParams ≤
      2^PrimT.C4Geo.dRow r.header.prepared.starParams :=
    Nat.pow_le_pow_right (by decide) r.header.prepared.starParams.centerBits_balanced.1
  apply native_square_prefix_centers _ _ hC
  intro high low
  change entryValue r high.val low.val = originalCenterValue r
    (low.val + 2^PrimT.C4Geo.dRow r.header.prepared.starParams * high.val)
  calc
    _ = Terms.eval (actualAtom r.toRowContext high.val low.val) r.terms := equalityValue r _ _
    _ = _ := by
      apply congrArg (fun atoms => Terms.eval atoms r.terms)
      exact (actualAtom_walkAtomPoint r.toRowContext high.val low.val).trans
        (congrArg (Cells.walkAtomPoint r.header.prepared.starParams (by decide : 0<4)
          (callPatterns r.header.call r.header.prepared
            (indexedWalk r.header.prepared.seedParameters.N r.walkCode)) (callAtoms r.header.call))
          (centerOf_major r.toRowContext high.val low).symm)

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: cropping the real native square
at the ORIGINAL center count yields exactly the finite Builder.center
sequence in its original ordinal order, even on bad witnesses. -/
theorem native_value_originalPrefix (r : StageTuple.TermCutRequest) :
    let U := 2^PrimT.C4Geo.dRow r.header.prepared.starParams
    (pvals false (fun high low : Fin U => entryValue r high.val low.val)).take
      (2^(r.header.call.n-r.header.parameters.k)) =
      List.ofFn (fun z : Fin (2^(r.header.call.n-r.header.parameters.k)) =>
        Terms.eval (Cells.walkAtomPoint r.header.prepared.starParams (by decide : 0<4)
          (callPatterns r.header.call r.header.prepared
            (indexedWalk r.header.prepared.seedParameters.N r.walkCode)) (callAtoms r.header.call)
          (Builder.center r.header.call r.header.prepared r.header.witness z)) r.terms) := by
  have hp := native_value_prefix r
  have hc := nativePrefix_count r.toRowContext
  dsimp only at hp ⊢
  have hprefix : (pvals false (fun high low :
      Fin (2^PrimT.C4Geo.dRow r.header.prepared.starParams) =>
        entryValue r high.val low.val)).take (2^(r.header.call.n-r.header.parameters.k)) =
      List.ofFn (fun z : Fin (2^(r.header.call.n-r.header.parameters.k)) =>
        originalCenterValue r z.val) := by
    simpa only [hc, Fin.val_cast] using hp
  rw [hprefix]
  apply congrArg List.ofFn
  funext z
  unfold originalCenterValue
  rw [Builder.center_eq_centerOf]

end NearQuarticWires.StageNativeMeaning
