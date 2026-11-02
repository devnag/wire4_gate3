import Proof.Quartic.StageCertNative.Table
import Proof.Quartic.StageCert.MomentNativeMeaning
import Proof.Quartic.StageCertTests.NativeSigned

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPrinter
open NearCubicGates.Close.TabMachine
open StageCertificateControl StageCert.Tokens

/-- `lem:print`, paper/paper.tex: the actual
custom-Phi weighted dominance table of the signed two-cut split is
exactly the original integer equality sum at every square entry. -/
theorem nativeStream_value (r : StagePrint.NativeStreamRequest)
    (row column : Fin r.matrix.U) :
    StagePrint.cutTable r.matrix row column=
      (r.cuts.map (fun c=>EquationRow.exactValue c
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.parameters) row.val)
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.parameters) column.val))).sum := by
  calc
    _=∑ i : Fin r.matrix.Gates,EquationRow.weakValue (r.matrix.cuts.get i)
        (r.matrix.phi row.val) (r.matrix.phi column.val) := by
      unfold StagePrint.cutTable SupplierPrinter.weightedDominance
      apply Finset.sum_congr rfl
      intro i _
      unfold EquationRow.weakValue
      rw [threshold_split_as_dominance]
      rfl
    _=((r.matrix.cuts).map (fun c=>EquationRow.weakValue c
        (r.matrix.phi row.val) (r.matrix.phi column.val))).sum := by
      rw [←List.sum_ofFn]
      change (List.ofFn (fun i : Fin r.matrix.cuts.length=>EquationRow.weakValue
        r.matrix.cuts[i.val] (r.matrix.phi row.val) (r.matrix.phi column.val))).sum=_
      have h:=List.map_ofFn (f:=fun i : Fin r.matrix.cuts.length=>r.matrix.cuts[i.val])
        (g:=fun c=>EquationRow.weakValue c (r.matrix.phi row.val) (r.matrix.phi column.val))
      rw [List.ofFn_getElem] at h
      exact congrArg List.sum h.symm
    _=_ := by
      change ((EquationRow.doubled false r.cuts).map (fun c=>EquationRow.weakValue c
        (r.matrix.phi row.val) (r.matrix.phi column.val))).sum=_
      rw [EquationRow.doubled_value]
      unfold MatrixScoreBatch.Request.phi
      rw [r.matrix_columns]

/-- `lem:print`, paper/paper.tex: the one global
native table is the exact signed sum of all original term tables,
without a certified-column or honest-witness hypothesis. -/
theorem actualTable_value {B1 B2 : ℕ} (r : IndexedRequest B1 B2)
    (row column : Fin (actualTable r).matrix.U) :
    StagePrint.cutTable (actualTable r).matrix row column=
      ∑ i : Fin (termCount r),(actualMoment r i).nativeTermValue row.val column.val := by
  change StagePrint.cutTable (wholeRequest r).matrix row column=_
  rw [nativeStream_value (wholeRequest r) row column]
  change (((List.ofFn fun i : Fin (termCount r)=>StagePrint.nativeEqualityCuts (termRequest r i)).flatten).map
    (fun c=>EquationRow.exactValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols (zeroMoment r).rules.starParams) row.val)
      (MatrixScorePhi.value (PrimT.C4Geo.cols (zeroMoment r).rules.starParams) column.val))).sum=_
  rw [List.map_flatten,List.sum_flatten,List.map_map,List.map_ofFn,List.sum_ofFn]
  rfl

end NearQuarticWires.StageCertNative
