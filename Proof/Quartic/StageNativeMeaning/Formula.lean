import Proof.Quartic.StageNativeMeaning.Terms
import Proof.Gates.Expand.Machine
import Proof.Quartic.StageRecovery.BoundedCoefficients

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StagePrint StagePrint.NativeMeaning

/-- `lem:print`, paper/paper.tex: the literal actual
native cut stream for any supplied Terms list retains the original
pooled Boolean polynomial at every custom-Phi entry. -/
theorem termStream_value (r : StageTuple.RowContext)
    (terms : Terms (17*(Builder.allGates r.header.call).length)) (row column : ℕ) :
    (((terms.flatMap (nativeTermCuts r)).map (fun c => EquationRow.exactValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum) =
      Terms.eval (actualAtom r row column) terms := by
  rw [listSum_flatMap]
  unfold Terms.eval
  congr 1
  apply List.map_congr_left
  intro t _
  exact nativeTermCuts_value r t row column

/-- `lem:print`, paper/paper.tex:
the ACTUAL exact expansion machine's Terms output gives the original
source Formula value on every custom-Phi entry, without a semantic
output promise, certificate or witness-honesty assumption. -/
theorem actualExpansion_value (r : StageTuple.RowContext)
    (F : Formula (17*(Builder.allGates r.header.call).length)) (row column : ℕ) :
    ((((NearCubicGates.Close.Expand.expansionMachine.expand ⟨_, F⟩).flatMap (nativeTermCuts r)).map
      (fun c => EquationRow.exactValue c
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum) =
      F.eval (boolPoint (actualAtom r row column)) :=
  (termStream_value r _ row column).trans
    ((NearCubicGates.Close.Expand.expansionMachine.ok ⟨_, F⟩).eval _)

/-- `lem:residue` and `lem:print`, paper/paper.tex: the ACTUAL bounded modular Terms retain the source
Formula modulo its original modulus at every native Phi entry,
including prime powers and uncertified columns. -/
theorem boundedModTerms_value (r : StageTuple.RowContext) (q : ℕ)
    (F : Formula (17*(Builder.allGates r.header.call).length)) (D : ℕ)
    (hD : F.degree ≤ D) (row column : ℕ) :
    ((((StageRecovery.boundedModTerms q F D).flatMap (nativeTermCuts r)).map
      (fun c => EquationRow.exactValue c
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
        (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum) ≡
      F.eval (boolPoint (actualAtom r row column)) [ZMOD (q : ℤ)] := by
  rw [termStream_value]
  exact StageRecovery.boundedModTerms_eval q F D hD _

/-- `lem:print`, paper/paper.tex: the real
original-to-successor two-weak-cut conversion preserves the exact
native polynomial value before any Greedy coefficient reduction. -/
theorem weakCuts_value (r : StageTuple.TermCutRequest) (row column : ℕ) :
    (((EquationRow.doubled false (nativeEqualityCuts r)).map (fun c => EquationRow.weakValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum) =
      Terms.eval (actualAtom r.toRowContext row column) r.terms := by
  rw [EquationRow.doubled_value]
  exact equalityValue r row column

end NearQuarticWires.StageNativeMeaning
