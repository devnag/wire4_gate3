import Proof.Quartic.StagePullback.NativeRow

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: a finite signed
field list is recovered exactly from its padded coordinate accessor. -/
theorem ofFn_getD_eq (zs : List ℤ) (N : ℕ) (h : zs.length = N) :
    List.ofFn (fun j : Fin N => zs.getD j.val 0) = zs := by
  apply List.ext_getElem
  · simpa using h.symm
  · intro i hi hj
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem zs 0 hj

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the emitted signed row is exactly the actual native
child's weights in native coordinate order followed by its target. -/
theorem signedRow_fields (q : PointRequest) (e : ExactThresholdGate q.parameters.n)
    (transpose : Bool) : signedRow q e transpose =
      List.ofFn (nativeChild q e transpose).weight ++ [(nativeChild q e transpose).target] := by
  have hr := routes_length_le q e transpose
  have hh : (Pool.padTo (PrimT.C4Geo.width q.parameters)
        (Pool.routeL (Pool.coords (sideList q transpose) (flipList q) e)) ++
      Pool.padTo (PrimT.C4Geo.width q.parameters)
        (Pool.routeR (Pool.coords (sideList q transpose) (flipList q) e))).length =
      PrimT.C4Geo.width q.parameters + PrimT.C4Geo.width q.parameters := by
    rw [List.length_append, Pool.padTo_length _ _ hr.1, Pool.padTo_length _ _ hr.2]
  unfold signedRow nativeChild Pool.pullDense
  congr 1
  exact (ofFn_getD_eq _ _ hh).symm

/-- `imp:pullback`, paper/paper.tex: the actual
row output is the exact field-record representation of the actual
native affine child, including its exact adjusted target. -/
theorem request_output_nativeChild (r : RowRequest) :
    r.output = NearCubicGates.Close.TabMachine.fieldsRecs r.Lout
      [List.ofFn (nativeChild r.point r.child r.transpose).weight ++
        [(nativeChild r.point r.child r.transpose).target]] := by
  rw [request_output_fieldsRecs, signedRow_fields]

end NearQuarticWires.StagePullback.NativeRows
