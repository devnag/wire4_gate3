import Proof.Quartic.StageTupleSetupCold.Finish

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StageTuple

namespace Helpers

/-- `lem:print` and `prop:time`, paper/paper.tex: the complete physical cold setup
starts at the unchanged original request with internally justified
blank private workspace. The exact frozen source bound charges every
small call, framing pass, Terms scan and sequencing instruction. -/
theorem program_run (F : Helpers) (r : TermCutRequest) :
    ∃τ,WXExec (capacity r) F.program (F.initial r) τ
      (sourceStepsWith F.widthBudget F.rowBudget F.coefficientBudget r) ∧
      τ.st (F.data 16)=frame r.preparedWord := by
  obtain ⟨σ,ep,hr,hcold⟩:=F.prelude_run r
  obtain ⟨τ,ef,ho⟩:=F.finish_run r σ hr hcold
  refine ⟨τ,(ep.seq ef).cast (capacity r) rfl ?_,ho⟩
  unfold finishSteps sourceStepsWith
  omega

/-- `lem:print`, paper/paper.tex: the
final prepared-output tape is distinct from the original input tape. -/
theorem output_ne_zero (F : Helpers) : (F.data 16).val≠0 :=by
  change (16 : ℕ)≠0
  decide

end Helpers

end NearQuarticWires.StageTupleSetupCold
