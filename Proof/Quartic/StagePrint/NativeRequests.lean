import Proof.Quartic.StagePrint.NativeGeometry
import Proof.Quartic.StagePrint.FullTable
import Proof.Supplier.EquationRowProducer

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

/-- `lem:print`, paper/paper.tex: the concatenated
actual equality stream carries one original star geometry and one
uniform signed field width; all census and fit fields are proof-only. -/
structure NativeStreamRequest where
  parameters : StarParams
  fieldWidth : ℕ
  cuts : List MatrixScoreBatch.Cut
  lengths : ∀ c∈cuts,c.leftWeights.length=PrimT.C4Geo.width parameters ∧
    c.rightWeights.length=PrimT.C4Geo.width parameters
  fits : ∀ c∈cuts,EquationRow.Fits fieldWidth c
  square : (2*cuts.length)*(2*cuts.length)≤rectangularInnerDimension (2^PrimT.C4Geo.dRow parameters)

/-- `lem:print`, paper/paper.tex: each exact
equation is represented by its original weak cut and its signed successor. -/
def NativeStreamRequest.matrix (r : NativeStreamRequest) : MatrixScoreBatch.Request where
  d:=PrimT.C4Geo.dRow r.parameters
  p:=r.fieldWidth+1
  cuts:=EquationRow.doubled false r.cuts
  width:=PrimT.C4Geo.width r.parameters
  column:=fun j=>(PrimT.C4Geo.cols r.parameters).getD j 0
  widthLe:=native_width_le_two_dimensions r.parameters
  columnFits:=fun j _=>native_column_fits r.parameters j
  lengths:=by
    intro c hc
    simp only [EquationRow.doubled,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hc
    obtain ⟨original,ho,hc⟩:=hc
    rcases hc with rfl|rfl <;> simpa [EquationRow.padded,EquationRow.paddedRight,EquationRow.successor] using r.lengths original ho
  fits:=by
    intro c hc
    simp only [EquationRow.doubled,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hc
    obtain ⟨original,ho,hc⟩:=hc
    rcases hc with rfl|rfl
    · simpa [EquationRow.Fits,EquationRow.padded,EquationRow.paddedRight] using EquationRow.fits_widen r.fieldWidth original (r.fits original ho)
    · simpa [EquationRow.Fits,EquationRow.padded,EquationRow.paddedRight,EquationRow.successor] using EquationRow.successor_fits r.fieldWidth original (r.fits original ho)
  gateSquare:=by rw [EquationRow.doubled_length];exact r.square

theorem NativeStreamRequest.matrix_cuts_length (r : NativeStreamRequest) :
    r.matrix.cuts.length=2*r.cuts.length := EquationRow.doubled_length _ _

/-- `lem:print`, paper/paper.tex: the actual
gate-square guard also bounds the native row-count metadata. -/
def NativeStreamRequest.table (r : NativeStreamRequest) : TableRequest where
  matrix:=r.matrix
  cuts_le:=by
    have hroot : rectangularInnerDimension r.matrix.U≤r.matrix.U := by
      apply integerCeilRoot_le (by decide : 0<10)
      exact Nat.le_self_pow (by decide) _
    have h:=r.matrix.gateSquare.trans hroot
    exact (Nat.le_mul_self _).trans h

theorem NativeStreamRequest.matrix_columns (r : NativeStreamRequest) :
    r.matrix.cols=PrimT.C4Geo.cols r.parameters := by
  apply List.ext_getElem
  · simp [MatrixScoreBatch.Request.cols,PrimT.C4Geo.cols,NativeStreamRequest.matrix]
  · intro i hi hj
    simp only [MatrixScoreBatch.Request.cols,NativeStreamRequest.matrix,List.getElem_map,List.getElem_range]
    exact List.getD_eq_getElem _ _ hj

/-- `lem:print`, paper/paper.tex: replacing the
identity-coordinate header leaves the actual two-cut body unchanged. -/
theorem NativeStreamRequest.matrix_header (r : NativeStreamRequest) :
    MatrixScoreBatch.header r.matrix=
      RepairRepresentation.natWord (PrimT.C4Geo.dRow r.parameters)++
      RepairRepresentation.natWord (r.fieldWidth+1)++
      RepairRepresentation.natWord (2*r.cuts.length)++
      RepairRepresentation.natWord (PrimT.C4Geo.width r.parameters)++
      MatrixScorePhi.columnsWord (PrimT.C4Geo.width r.parameters) (PrimT.C4Geo.cols r.parameters) := by
  unfold MatrixScoreBatch.header MatrixScoreBatch.Request.Gates
  rw [r.matrix_cuts_length,r.matrix_columns]
  rfl

/-- `lem:print`, paper/paper.tex: the existing
cold two-cut machine can use its dense-coordinate dimension without
performing a table evaluation or changing any original equality. -/
def NativeStreamRequest.equalityInput (r : NativeStreamRequest) : EquationRow.Input where
  d:=PrimT.C4Geo.width r.parameters
  p:=r.fieldWidth
  odd:=false
  cuts:=r.cuts
  lengths:=by intro c hc;simpa using r.lengths c hc
  fits:=r.fits
  oddPositive:=by simp
  gateSquare:=by
    apply r.square.trans
    apply integerCeilRoot_le (by decide : 0<10)
    exact (Nat.pow_le_pow_right (by decide : 0<2) (native_dimension_le_width r.parameters)).trans
      (le_integerCeilRoot_pow (by decide : 0<10))

/-- `lem:print`, paper/paper.tex: the reused
cold two-cut machine emits the identical body used by the common-phi request. -/
theorem NativeStreamRequest.equality_body (r : NativeStreamRequest) :
    (EquationRow.request r.equalityInput).cuts=r.matrix.cuts := rfl

end NearQuarticWires.StagePrint
