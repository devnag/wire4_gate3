import Proof.Quartic.StagePrep.OriginalExecution
import Proof.Quartic.StagePrep.PublicPrefix

/-!
# The complete physical preparation stage

Paper: the encoded requests of `thm:counter`, paper/paper.tex, the witness prefix, and
`prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open NearCubicWires.RepairOrdinary

/-- A fixed register-width constant for the actual preparation
program of `prop:time`, paper/paper.tex. -/
noncomputable def preparationWidthConstant (B1 B2 : ℕ) : ℕ :=
  Classical.choose (originalPreparationExecution B1 B2)

/-- The exact all-call execution property of the selected
fixed width, `prop:time`, paper/paper.tex. -/
theorem preparationWidthConstant_spec (B1 B2 : ℕ) :
    1 ≤ preparationWidthConstant B1 B2 ∧ ∀ (c : Call) (w : List Bool),
      ∃ b n, Ex (ctxOf (preparationWidthConstant B1 B2) (callWord c) w)
        (rawPreparationProgram B1 B2) a0 b n ∧
        b.out=Program.prepWord B1 B2 c w ∧
        n ≤ rawPreparationCost B1 B2
          (wdOf (preparationWidthConstant B1 B2) (callWord c).length) c ∧
        b.wq ≤ 5*(c.n+1)^5 :=
  Classical.choose_spec (originalPreparationExecution B1 B2)

/-- The actual physical preparation clock of `prop:time`,
paper/paper.tex, depends only on the original
call word, independently of the witness suffix. -/
noncomputable def prepBudget (B1 B2 : ℕ) : Call → List Bool → ℕ :=
  nativePreparationBudget (preparationWidthConstant B1 B2)
    (rawPreparationMajorant B1 B2 (preparationWidthConstant B1 B2))

/-- The actual complete preparation WordFunction of
`thm:counter` and `prop:time`, paper/paper.tex. It parses and checks the original call,
executes the literal canonical selector on all relevant paths,
prints the whole selected record, and reads only the public
zero-filled witness prefix. -/
noncomputable def prep (B1 B2 : ℕ) :
    WordFunction (Call×List Bool) Program.requestWord
      (fun r => frame (Program.prepWord B1 B2 r.1 r.2))
      (fun r => prepBudget B1 B2 r.1 r.2) :=
  preparationWordFunction_of_raw_execution B1 B2 (preparationWidthConstant B1 B2)
    (preparationWidthConstant_spec B1 B2).1
    (rawPreparationMajorant B1 B2 (preparationWidthConstant B1 B2))
    (by
      intro c w
      obtain ⟨b,n,hex,hout,hn,_⟩ := (preparationWidthConstant_spec B1 B2).2 c w
      exact ⟨b,n,hex,hout,hn.trans (rawPreparationCost_le B1 B2 _ c)⟩)

/-- The complete physical preparation stage satisfies the
all-calls polynomial clock required by `prop:time`,
paper/paper.tex, for every witness word. -/
theorem prepCost (B1 B2 : ℕ) : Program.PolyCost (prepBudget B1 B2) :=
  nativePreparationBudget_poly _ _ (rawPreparationMajorant_poly B1 B2 _)

end NearQuarticWires.StagePrep
