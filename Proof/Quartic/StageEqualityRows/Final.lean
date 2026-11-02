import Proof.Quartic.StageEqualityRows.StripCost

set_option autoImplicit false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5
open StagePrint StagePrint.Downstream

/-- `prop:time`, paper/paper.tex: all actual
per-walk acquisition, equality splitting, header removal and framed
output clocks have quadratic dependence on that same stream. -/
theorem rowBudget_quadratic (r : NativeStreamRequest) : rowBudget r≤10^9*quadraticScale r := by
  have hf:=formatterSteps_le r
  have he:=equalityBudget_le r
  have hs:=stripperSteps_le r
  have h1:1≤quadraticScale r:=(scale_bounds r).1
  unfold rowBudget constructionBudget
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual ordinary constructor satisfies the fixed
per-walk quadratic stream budget used by the native printer. -/
theorem rowBudget_le (r : NativeStreamRequest) : rowBudget r≤
    10^30*(PrimT.C4Geo.width r.parameters+r.fieldWidth+2)^20*
      ((r.cuts.flatMap (MatrixScoreBatch.cutWord r.fieldWidth)).length+1)^2 := by
  have h:=rowBudget_quadratic r
  have hA:1≤widthScale r:=by unfold widthScale;omega
  have hp : widthScale r^2≤widthScale r^20 := Nat.pow_le_pow_right hA (by decide)
  calc
    rowBudget r≤10^9*quadraticScale r := h
    _≤10^30*widthScale r^20*streamScale r^2 := by
      have hc : (10 : ℕ)^9≤10^30 := Nat.pow_le_pow_right (by decide) (by decide)
      have hh := Nat.mul_le_mul_right (streamScale r^2) (Nat.mul_le_mul hc hp)
      simpa only [quadraticScale,Nat.mul_assoc] using hh
    _=_ := rfl

/-- `prop:time`, paper/paper.tex: a larger
proved clock preserves the very same ordinary program and output. -/
noncomputable def enlargeBudget {Request : Type} {input output : Request → List Bool}
    {old new : Request → ℕ} (f : WordFunction Request input output old)
    (hbound : ∀ r,old r≤new r) : WordFunction Request input output new where
  program:=f.program
  realizes:=by
    intro r
    obtain ⟨receipt,hr,ho⟩:=f.realizes r
    have hm:=run_moreFuel f.program.machine (old r) (new r-old r)
      (f.program.inputTapes (input r)) receipt hr
    rw [Nat.add_sub_of_le (hbound r)] at hm
    exact ⟨receipt,hm,ho⟩

/-- `lem:print`, paper/paper.tex: one complete
cold ordinary program maps the actual raw equality fields and unary
widths to the exact framed signed weak rows. The row count, header
boundary and all copied bytes are obtained by physical execution. -/
noncomputable def equalityRowsPrinter : EqualityRowsPrinter :=
  enlargeBudget rowWordFunction rowBudget_le

end NearQuarticWires.StageEqualityRows
