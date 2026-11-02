import Proof.Quartic.StagePrep.CanonicalCost
import Proof.Quartic.StagePrep.OutputCost

/-!
# The canonical preparation and output clock

Paper: `sec:params`, paper/paper.tex, and
the preparation cost in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic
open Classical

/-- The complete parameter and output charge in `prop:time`,
paper/paper.tex, includes the selected writer
only when the literal canonical selection succeeds. -/
noncomputable def canonicalExitCost (c : Call) (Wd : ℕ) : ℕ :=
  canonicalPreparationBudget (Builder.callInput c) c.radius.num.natAbs c.radius.den +
    (match Cells.prepare (Builder.callInput c) with
      | some p => successOutputCost c p Wd
      | none => 0) + 200

/-- All canonical preparation exits in `prop:time`,
paper/paper.tex, have an original-call
polynomial envelope on admitted nonzero-wire calls. -/
theorem canonicalExitCost_le (B1 B2 : ℕ) (c : Call) (Wd : ℕ)
    (ha : Transfer.Admitted4 B1 B2 c) (hW : Transfer.callWires c≠0) :
    canonicalExitCost c Wd ≤ canonicalBudgetMajorant B1 (callWord c).length+
      successOutputMajorant (callWord c).length Wd+200 := by
  let x := Builder.callInput c
  let L := (callWord c).length
  have hn : c.n ≤ L := n_le_callWord B1 B2 c
    (Program.admitted_of_admitted4 ha) (Cells.admitted4_nonzero_topWeight ha hW)
  have hv : ValidInput x := Cells.callInput_valid c ha hW
  have hb : 1 ≤ c.radius*(c.n:ℚ)^B1 := ha.2.2.2.2.2.2.2.2.2.1
  have hbits := call_bounds c
  have hnp : 0<c.radius.num := Rat.num_pos.mpr hv.2.2.2.2.1
  have hnum : x.beta.num=(c.radius.num.natAbs:ℕ) := by
    change c.radius.num=(_ : ℤ)
    rw [Int.natCast_natAbs,abs_of_pos hnp]
  have hc := canonicalPreparationBudget_le x hv B1 L _ _ hn hb hnum rfl
    hbits.2.2.2.1.le hbits.2.2.2.2.1.le
  change canonicalPreparationBudget (Builder.callInput c) c.radius.num.natAbs c.radius.den ≤
    canonicalBudgetMajorant B1 (callWord c).length at hc
  unfold canonicalExitCost
  cases hp : Cells.prepare (Builder.callInput c) with
  | none =>
    simp only
    omega
  | some p =>
    have ho := successOutputCost_le c p (Cells.prepare_spec _ _ hp) L Wd hn le_rfl
    exact Nat.add_le_add_right (Nat.add_le_add hc ho) 200

end NearQuarticWires.StagePrep
