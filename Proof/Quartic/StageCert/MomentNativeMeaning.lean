import Proof.Quartic.StageCert.MomentNativeContext

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Tabulator
open StagePrint StageNativeMeaning

/-- `lem:print`, paper/paper.tex: this is the
actual exact expansion machine's original-child equality stream,
evaluated using the same common-Phi matrix coordinates as native printing. -/
noncomputable def MomentRequest.nativeTermValue {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (row column : ℕ) : ℤ :=
  (((NearCubicGates.Close.Expand.expansionMachine.expand ⟨_,r.formula⟩).flatMap
    (nativeTermCuts r.nativeContext)).map (fun cut=>EquationRow.exactValue cut
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.rules.starParams) row)
      (MatrixScorePhi.value (PrimT.C4Geo.cols r.rules.starParams) column))).sum

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: the actual native
per-term equality stream equals the original signed source term
at the literal low-column/high-row Builder center, on every bad column. -/
theorem MomentRequest.nativeTermValue_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (row : Fin (2^PrimT.C4Geo.dR r.rules.starParams))
    (column : Fin (2^PrimT.C4Geo.dRow r.rules.starParams)) :
    r.nativeTermValue row.val column.val=
      r.termValue (centerIndex r.call r.rules column row) := by
  exact (StageNativeMeaning.actualExpansion_value r.nativeContext r.formula row.val column.val).trans
    (congrArg r.formula.eval (r.native_atoms_eq row column))

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: concatenating the actual exact
per-term equality streams gives the original whole-test signed entry,
with population N² and moment N⁸ indices kept distinct. -/
theorem MomentRequest.nativeTermValue_sum_eq_actualTestTable {B1 B2 : ℕ}
    (r : MomentRequest B1 B2)
    (row : Fin (2^PrimT.C4Geo.dR r.rules.starParams))
    (column : Fin (2^PrimT.C4Geo.dRow r.rules.starParams)) :
    (∑ i : Fin (momentTermCount r.selected.1.N r.test),
      (r.withIndex i).nativeTermValue row.val column.val)=
      (StageCertTests.actualTestTable r.call r.rules r.witness r.test.kind
        (centerIndex r.call r.rules column row)).1 := by
  classical
  calc
    _=∑ i : Fin (momentTermCount r.selected.1.N r.test),
        (r.withIndex i).termValue (centerIndex r.call r.rules column row) :=
      Finset.sum_congr rfl (fun i _=>(r.withIndex i).nativeTermValue_eq row column)
    _=_ := r.term_sum_eq_actualTestTable (centerIndex r.call r.rules column row)

end NearQuarticWires.StageCert.Tokens
