import Proof.Quartic.StagePrint.NativeEquations

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.NativeMeaning

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ThresholdCompiler
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex:
the actual low-first walk addresses the original star-error patterns. -/
def actualWalk (r : StageTuple.RowContext) : Fin 8 → StarParams.Errors r.header.prepared.starParams :=
  fun slot=>(SeedFix.callEqv r.header.prepared.starParams).symm
    (finCongr (Builder.seedN_eq_patternCodes r.header.call r.header.prepared)
      (indexedWalk r.header.prepared.seedParameters.N r.walkCode slot))

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the original Boolean atom at the literal common-phi
center, with the physical native transpose applied once. -/
def actualAtom (r : StageTuple.RowContext) (row column : ℕ)
    (i : Fin (17*(Builder.allGates r.header.call).length)) : Bool :=
  (callAtoms r.header.call (r.originalIndex i)).eval
    (Header.numericRolePoint r.header.prepared.starParams (actualWalk r) (r.role i)
      (PrimT.C4Geo.centerAt r.header.prepared.starParams
        (Builder.translation r.header.call r.header.prepared r.header.witness) column row))

/-- `lem:print`, paper/paper.tex: exact weighted
native equations evaluate the original pooled Boolean polynomial at
every common-phi matrix entry, including all uncertified columns. -/
def EqualityValue : Prop :=
  ∀ (r : StageTuple.TermCutRequest) (row column : ℕ),
    ((nativeEqualityCuts r).map (fun c=>EquationRow.exactValue c
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.header.prepared.starParams) column))).sum=
      Terms.eval (actualAtom r.toRowContext row column) r.terms

#check (actualWalk : (r : StageTuple.RowContext) → Fin 8 → StarParams.Errors r.header.prepared.starParams)
#check (actualAtom : (r : StageTuple.RowContext) → ℕ → ℕ →
  Fin (17*(Builder.allGates r.header.call).length) → Bool)
#check EqualityValue

end NearQuarticWires.StagePrint.NativeMeaning
