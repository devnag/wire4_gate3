import Proof.Quartic.StageMainMask.PointAppend
import Proof.Quartic.StageMainMask.PointData

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePullback

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the full coordinate accumulator has exactly its
binary registers, loop coordinate and the actual point-bit scratch. -/
def pointPackingScratch : List (Fin VV) :=
  [packedPointRegister, packedPointPower, MarkerCalls.originalCoordinate, vJ] ++ pointBitScratch

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: point accumulation preserves every actual scalar
metadata field used by the next original coordinate. -/
theorem PointData.framePacking {a b : DS VV MM} {q : PointRequest}
    (h : PointData a q) (hf : Fr a b pointPackingScratch) : PointData b q := by
  exact ⟨h.constants.of_fr hf (by decide),
    fun i => (hf _ (by fin_cases i <;> decide)).trans (h.fields i),
    (hf _ (by decide)).trans h.useLeft, (hf _ (by decide)).trans h.useRight,
    (hf _ (by decide)).trans h.half, (hf _ (by decide)).trans h.blockWidth,
    (hf _ (by decide)).trans h.radix⟩

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: one actual coordinate is computed by the
canonical center and affine-bit programs, then appended physically. -/
def pointPackingStep : St VV MM := .seq pointBitProgram appendPointBit

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: one charged iteration advances
the exact original-point prefix and preserves all retained metadata. -/
theorem pointPackingStep_run (C : Ctx) (q : PointRequest) (k : ℕ) (hk : k < q.parameters.n)
    (a : DS VV MM) (hi : PointData a q)
    (hcoord : a.env MarkerCalls.originalCoordinate = k)
    (hv : a.env packedPointRegister = pointPrefix q k)
    (hp : a.env packedPointPower = 2 ^ k) (hwidth : q.parameters.n + 4 ≤ C.Wd) :
    Hs C pointPackingStep a (500 * (q.parameters.n + 1) ^ 3 + 5) (fun b =>
      b.env packedPointRegister = pointPrefix q (k + 1) ∧
      b.env packedPointPower = 2 ^ (k + 1) ∧ PointData b q ∧ b.sh = a.sh ∧
      b.env MarkerCalls.originalCoordinate = a.env MarkerCalls.originalCoordinate ∧
      Fr a b pointPackingScratch) := by
  have hdata (i : Fin 9) := hi.fields i
  have hn : a.env 20 = q.parameters.n := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdata 0
  have hr : a.env 21 = q.parameters.r := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdata 1
  have hb : a.env 22 = q.parameters.b := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdata 2
  have hs : a.env 23 = q.parameters.s := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdata 3
  have hrow : a.env 25 = q.row.val := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdata 5
  have hcol : a.env 26 = q.column.val := by
    simpa [VV, pointFieldRegister, PointRequest.fields] using hdata 6
  have hcost : 300 * (q.parameters.n + 1) ^ 3 + 21 * (k / q.parameters.b) + 125 ≤
      500 * (q.parameters.n + 1) ^ 3 := by
    have hd := Nat.div_le_self k q.parameters.b
    have hp3 : q.parameters.n + 1 ≤ (q.parameters.n + 1) ^ 3 := Nat.le_self_pow (by decide) _
    omega
  unfold pointPackingStep
  refine Hs.seq (t1 := 500 * (q.parameters.n + 1) ^ 3) (t2 := 4)
    ((pointBitProgram_run C a q ⟨k, hk⟩ (hi.inputs _ hcoord) hn hr hb hs hrow hcol hwidth).mono
      hcost (fun _ h => h)) ?_
  rintro b ⟨hbvalue, hbsh, hbfr⟩
  have hbf : Fr a b pointPackingScratch := hbfr.weaken (fun _ hx => List.mem_append_right _ hx)
  have hbi : PointData b q := hi.framePacking hbf
  refine (appendPointBit_run C q k hk b hbi.constants hbvalue
    ((hbfr _ (by decide)).trans hv) ((hbfr _ (by decide)).trans hp) hwidth).mono le_rfl ?_
  rintro d ⟨hdv, hdp, hdsh, _hdc, hdfr⟩
  have hdf : Fr b d pointPackingScratch := hdfr.weaken (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide)
  exact ⟨hdv, hdp, hbi.framePacking hdf, hdsh.trans hbsh,
    (hdfr _ (by decide)).trans (hbfr _ (by decide)), hbf.trans hdf⟩

end NearQuarticWires.StageMainMask
