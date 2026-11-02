import Proof.Quartic.StageNativeMeaning.Children

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Tabulator
open StagePrint StagePrint.NativeMeaning

def nativeTermCuts (r : StageTuple.RowContext)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ) : List MatrixScoreBatch.Cut :=
  (tuples ((t.1.sort (· ≤ ·)).map (nativeKidsEquations r))).map fun es =>
    RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)

/-- `imp:stack` and `lem:print`, paper/paper.tex: every actual child tuple contributes exactly its original
Boolean monomial at the literal shared-Phi entry, including empty tuples. -/
theorem nativeTermCuts_value (r : StageTuple.RowContext)
    (t : Finset (Fin (17*(Builder.allGates r.header.call).length)) × ℤ) (row column : ℕ) :
    ((nativeTermCuts r t).map (fun c => EquationRow.exactValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum =
      t.2 * monomialValue (actualAtom r row column) t.1 := by
  let aL := MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row
  let aR := MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column
  unfold nativeTermCuts
  rw [List.map_map]
  have hc : ((fun c => EquationRow.exactValue c aL aR) ∘
      fun es : List (NativeHalfEquation r) =>
        RowBinLift.split t.2 (SupplierEstimator.canonicalEquationStack es)) =
      fun es => t.2 * ((es.all fun e => decide (e.Holds (RowBinLift.assignment aL aR))).toNat : ℤ) := by
    funext es
    simp only [Function.comp_apply, RowBinLift.split_value, RowBinLift.stack_all]
  rw [hc, List.sum_map_mul_left, tuples_sum, List.map_map]
  congr 1
  have hk : ((fun es : List (NativeHalfEquation r) =>
      (es.map fun e => ((decide (e.Holds (RowBinLift.assignment aL aR))).toNat : ℤ)).sum) ∘
        nativeKidsEquations r) = fun i => ((actualAtom r row column i).toNat : ℤ) := by
    funext i
    exact nativeChildren_sum r i row column
  rw [hk, prod_toNat]
  unfold monomialValue
  simp only [Finset.mem_sort]

/-- `lem:print`, paper/paper.tex: the ACTUAL
native equality-cut list evaluates the original pooled polynomial on
its concrete custom Phi at every row and column, with no certificate
or witness-honesty condition and no replacement tabulation model. -/
theorem equalityValue : EqualityValue := by
  intro r row column
  change (((r.terms.flatMap (nativeTermCuts r.toRowContext)).map
    (fun c => EquationRow.exactValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum) = _
  rw [listSum_flatMap]
  unfold Terms.eval
  congr 1
  apply List.map_congr_left
  intro t _
  exact nativeTermCuts_value r.toRowContext t row column

end NearQuarticWires.StageNativeMeaning
