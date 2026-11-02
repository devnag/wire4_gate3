import Proof.Quartic.StageTupleSetupCold.Execution

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab
open StageTuple

/-- `lem:print`, paper/paper.tex: all
four small calls use the genuine closed ordinary width, row-count and
coefficient programs and their own complete declared budgets. -/
noncomputable def actualHelpers : Helpers where
  widthBudget:=StageTupleSetup.widthBudget
  width:=StageTupleSetup.widthWordFunction
  rowBudget:=StageNativeRowCount.Request.budget
  row:=StageNativeRowCount.rowCountWordFunction
  coefficientBudget:=CoefficientRequest.budget
  coefficient:=coefficientWordFunction

/-- `prop:time`, paper/paper.tex: the
closed physical helper instantiation uses the exact frozen source
clock, including both genuine fixed coefficient calls. -/
theorem actual_sourceSteps (r : TermCutRequest) :
    sourceStepsWith actualHelpers.widthBudget actualHelpers.rowBudget actualHelpers.coefficientBudget r=
      sourceSteps r :=rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete actual cold setup
starts from the unchanged original eleven-field Tuple request and
prints its exact framed prepared word. All original Terms bytes,
small ordinary calls, internal blank margins and the final global
head reset are paid by the same setupBudget. No allocator, decoded
input, cached helper result, program or producer is an extra premise. -/
noncomputable def tupleSetupWordFunction :
    WordFunction TermCutRequest TermCutRequest.word
      (fun r=>frame r.preparedWord) setupBudget :=
  wordFunction_of_ideal actualHelpers.program (actualHelpers.data 16)
    actualHelpers.output_ne_zero capacity actualHelpers.lens sourceSteps (fun _=>le_rfl) (by
      intro r
      obtain ⟨τ,he,ho⟩:=actualHelpers.program_run r
      rw [actual_sourceSteps r] at he
      exact ⟨actualHelpers.lens_output r,τ,he,ho⟩)

end NearQuarticWires.StageTupleSetupCold
