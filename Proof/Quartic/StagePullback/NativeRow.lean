import Proof.Quartic.StagePullback.RowRequest
import Proof.Gates.TabMachine.Tuple

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms

/-- `imp:pullback`, paper/paper.tex: the actual
canonical original-coordinate side list, exchanged for transposed native
column order exactly when requested. -/
def sideList (q : PointRequest) (transpose : Bool) : List Bool :=
  List.ofFn fun x : Fin q.parameters.n => xor (q.parameters.centerSide x) transpose

/-- `imp:pullback`, paper/paper.tex: the actual
canonical original-coordinate translation and selected error flips. -/
def flipList (q : PointRequest) : List Bool := List.ofFn q.flip

def coordinateRecords (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) : List Pool.Coord :=
  (List.range q.parameters.n).map fun i =>
    (coordinateSide q transpose i, coordinateFlip q i, originalWeight q e i)

/-- `imp:pullback`, paper/paper.tex: native pullback
records are exactly the actual original-coordinate records built by the
physical signed row loop. -/
theorem coords_coordinateRecords (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) :
    Pool.coords (sideList q transpose) (flipList q) e = coordinateRecords q e transpose := by
  apply List.ext_getElem
  · simp [Pool.coords, coordinateRecords]
  · intro i hi hj
    have hi' : i < q.parameters.n := by simpa [Pool.coords] using hi
    have hs : (sideList q transpose).getD i false = xor (q.parameters.centerSide ⟨i, hi'⟩) transpose :=
      PrimT.C4Geo.ofFn_getD (fun x : Fin q.parameters.n => xor (q.parameters.centerSide x) transpose) ⟨i, hi'⟩
    have hf : (flipList q).getD i false = q.flip ⟨i, hi'⟩ :=
      PrimT.C4Geo.ofFn_getD q.flip ⟨i, hi'⟩
    simp only [Pool.coords, coordinateRecords, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    rw [hs, hf]
    simp only [coordinateSide, coordinateFlip, originalWeight, dif_pos hi']

/-- `imp:pullback`, paper/paper.tex: the actual
physical left-store encodings equal the canonical signed left routing. -/
theorem rowNumbers_routeL (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) : rowNumbers q e transpose true q.parameters.n =
      (Pool.routeL (Pool.coords (sideList q transpose) (flipList q) e)).map SInt.encS := by
  rw [coords_coordinateRecords]
  simp [Pool.routeL, coordinateRecords, rowNumbers, List.filter_map, List.map_map,
    Function.comp_def, Pool.flipW]

/-- `imp:pullback`, paper/paper.tex: the actual
physical right-store encodings equal the canonical signed right routing. -/
theorem rowNumbers_routeR (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) : rowNumbers q e transpose false q.parameters.n =
      (Pool.routeR (Pool.coords (sideList q transpose) (flipList q) e)).map SInt.encS := by
  rw [coords_coordinateRecords]
  simp [Pool.routeR, coordinateRecords, rowNumbers, List.filter_map, List.map_map,
    Function.comp_def, Pool.flipW]

/-- `imp:pullback`, paper/paper.tex: exact physical
target correction is the canonical sum of original flipped coefficients. -/
theorem targetPrefix_flipSum (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) : targetPrefix q e q.parameters.n =
      Pool.flipSum (Pool.coords (sideList q transpose) (flipList q) e) := by
  rw [coords_coordinateRecords]
  simp [targetPrefix, Pool.flipSum, coordinateRecords, List.map_map, Function.comp_def]

/-- `imp:pullback`, paper/paper.tex: actual native
side counts give the canonical dense-child route-length guards. -/
theorem routes_length_le (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) :
    (Pool.routeL (Pool.coords (sideList q transpose) (flipList q) e)).length ≤ PrimT.C4Geo.width q.parameters ∧
    (Pool.routeR (Pool.coords (sideList q transpose) (flipList q) e)).length ≤ PrimT.C4Geo.width q.parameters := by
  have hl := rowNumbers_length_le q e transpose true
  have hr := rowNumbers_length_le q e transpose false
  rw [rowNumbers_routeL, List.length_map] at hl
  rw [rowNumbers_routeR, List.length_map] at hr
  exact ⟨hl, hr⟩

/-- `imp:pullback`, paper/paper.tex: the exact
canonical dense affine child, using the actual side and error metadata. -/
def nativeChild (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (transpose : Bool) :
    ExactThresholdGate (PrimT.C4Geo.width q.parameters + PrimT.C4Geo.width q.parameters) :=
  Pool.pullDense (sideList q transpose) (flipList q) (PrimT.C4Geo.width q.parameters) e

/-- `imp:pullback` and `lem:print`, paper/paper.tex: exact signed fields of the actual native dense child. -/
def signedRow (q : PointRequest) (e : ExactThresholdGate q.parameters.n) (transpose : Bool) : List ℤ :=
  Pool.padTo (PrimT.C4Geo.width q.parameters)
      (Pool.routeL (Pool.coords (sideList q transpose) (flipList q) e)) ++
    Pool.padTo (PrimT.C4Geo.width q.parameters)
      (Pool.routeR (Pool.coords (sideList q transpose) (flipList q) e)) ++
    [e.target - Pool.flipSum (Pool.coords (sideList q transpose) (flipList q) e)]

/-- `lem:print`, paper/paper.tex: literal native
zero padding agrees with exact signed zero encoding. -/
theorem padTo_encS (W : ℕ) (zs : List ℤ) :
    (Pool.padTo W zs).map SInt.encS = padNumbers W (zs.map SInt.encS) := by
  simp [Pool.padTo, padNumbers, List.map_append, List.map_replicate]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: every physically emitted coefficient and target is the
exact canonical signed field of the actual dense affine child. -/
theorem request_numbers_signedRow (r : RowRequest) :
    r.numbers = (signedRow r.point r.child r.transpose).map SInt.encS := by
  have hl := rowNumbers_routeL r.point r.child r.transpose
  have hr := rowNumbers_routeR r.point r.child r.transpose
  have ht := targetPrefix_flipSum r.point r.child r.transpose
  simp only [RowRequest.numbers, signedRow, List.map_append, List.map_cons, List.map_nil,
    padTo_encS]
  dsimp only [RowRequest.point] at hl hr ht ⊢
  rw [hl, hr, ht]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the cold row compiler's output is byte-for-byte the
native signed affine row's exact field-record stream. -/
theorem request_output_fieldsRecs (r : RowRequest) :
    r.output = NearCubicGates.Close.TabMachine.fieldsRecs r.Lout [signedRow r.point r.child r.transpose] := by
  unfold RowRequest.output
  rw [request_numbers_signedRow]
  simp only [NearCubicGates.Close.TabMachine.fieldsRecs, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.flatMap_map]
  rfl

end NearQuarticWires.StagePullback.NativeRows
