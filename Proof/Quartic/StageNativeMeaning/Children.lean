import Proof.Quartic.StageNativeMeaning.Points

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Tabulator
open StagePrint StagePrint.NativeMeaning

/-- `imp:disjoint`, paper/paper.tex: the original
exact child has its literal zero-one equation indicator. -/
theorem childGate_testValue {n : ℕ} (e : ExactEquation n) (point : BitInput n) :
    (((Cells.childGate e).eval point).toNat : ℤ) = testValue e point := by
  change ((decide (e.Holds point)).toNat : ℤ) = testValue e point
  by_cases h : e.Holds point <;> simp [h, testValue]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the typed native half-equation reads the same actual
custom-Phi assignment as the dense native child. -/
theorem toHalves_native_eval {width : ℕ} (e : ExactThresholdGate (width+width))
    (row column : ℕ) :
    decide ((toHalves (equationOfNativeGate e)).Holds (RowBinLift.assignment row column)) =
      e.eval (Pool.centerInput width row column) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, toHalves_holds, outerPoint_centerInput,
    equationOfNativeGate, ExactEquation.Holds, ExactThresholdGate.eval]
  rfl

/-- `imp:disjoint`, `imp:pullback` and `lem:print`, paper/paper.tex: summing the actual original-child pool
recovers its original threshold atom on every custom-Phi entry. Empty
pools and inclusive ties retain their original disjoint-child semantics. -/
theorem nativeChildren_sum (r : StageTuple.RowContext)
    (i : Fin (17*(Builder.allGates r.header.call).length)) (row column : ℕ) :
    ((nativeKidsEquations r i).map (fun e =>
      ((decide (e.Holds (RowBinLift.assignment
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column)))).toNat : ℤ))).sum =
      ((actualAtom r row column i).toNat : ℤ) := by
  let g := callAtoms r.header.call (r.originalIndex i)
  let point : BitInput r.header.call.n := Header.numericRolePoint r.header.prepared.starParams (actualWalk r) (r.role i)
    (PrimT.C4Geo.centerAt r.header.prepared.starParams
      (Builder.translation r.header.call r.header.prepared r.header.witness) column row)
  have hchild : ∀ j : Fin (exactChildren g).length,
      ((decide ((toHalves (equationOfNativeGate (r.originalRow i j).nativeChild)).Holds
        (RowBinLift.assignment
          (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
          (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column)))).toNat : ℤ) =
        testValue (exactChildren g)[j.val] point := by
    intro j
    have h0 := toHalves_native_eval (r.originalRow i j).nativeChild
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column)
    have h1 := originalRow_eval r i j row column
    exact (congrArg (fun b : Bool => (b.toNat : ℤ)) (h0.trans h1)).trans
      (childGate_testValue _ _)
  unfold nativeKidsEquations
  rw [List.map_ofFn]
  have he : List.ofFn (fun j : Fin (exactChildren g).length =>
      ((decide ((toHalves (equationOfNativeGate (r.originalRow i j).nativeChild)).Holds
        (RowBinLift.assignment
          (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
          (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column)))).toNat : ℤ)) =
      (exactChildren g).map (fun e => testValue e point) := by
    exact (congrArg List.ofFn (funext hchild)).trans (List.ofFn_getElem_eq_map (exactChildren g) (fun e => testValue e point))
  calc
    _ = ((exactChildren g).map (fun e => testValue e point)).sum := congrArg List.sum he
    _ = (if g.eval point then (1 : ℤ) else 0) := exactChildren_sum _ _
    _ = _ := by
      change (if g.eval point then (1 : ℤ) else 0) = ((g.eval point).toNat : ℤ)
      cases g.eval point <;> rfl

end NearQuarticWires.StageNativeMeaning
