import Proof.Quartic.StageLift.SourceMachine
import Proof.Quartic.StageRecovery.OutputFrame

set_option autoImplicit false

namespace NearQuarticWires.StageCompiledTerms

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- Step 3 and `prop:time`, paper/paper.tex: real source markers and the final handoff delimiter
are charged in the source's complete ordinary-machine clock. -/
noncomputable def framedSourceBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  langBudget (StageCert.Tokens.structuralSourceCallee B1 B2) (StageLift.printSourceSizes B1 B2)
    VV MM (Greedy.printInput r) (3*StageLift.sourceProgramSteps r+2)

/-- Step 3 and `lem:print`, paper/paper.tex: the complete original-input source executes physically
and frames its one-copy preparation carrier for the batch compiler. -/
noncomputable def framedSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) Greedy.printInput
      (fun r=>frame (StageLift.sourceCarrierWord r)) framedSourceBudget :=
  wordFunction_of_lang Greedy.printInput (fun r=>frame (StageLift.sourceCarrierWord r))
    (StageCert.Tokens.structuralSourceCallee B1 B2) (StageLift.printSourceSizes B1 B2)
    (StageRecovery.OutputFrame.framedProgram StageLift.printFormulaSourceProgram)
    (fun r=>3*StageLift.sourceProgramSteps r+2) (by
      intro r
      obtain ⟨b,n,he,hn,hout⟩:=StageLift.printFormulaSourceProgram_spec r
      have hf:=StageRecovery.OutputFrame.framedProgram_spec he
      have hzero : StageRecovery.OutputFrame.markedState (a0 : DS VV MM)=a0:=rfl
      rw [hzero] at hf
      exact ⟨StageRecovery.OutputFrame.framedState b,3*n+2,hf,
        by simpa only [StageRecovery.OutputFrame.framedState] using congrArg frame hout,
        by omega⟩) (by
      intro r
      have h:=StageLift.printSourceSizes_width r []
      have hp : 1≤(StageLift.sourceEnvelope r+1)^2:=Nat.pow_pos (by omega)
      simpa only [List.append_nil] using (show 1≤
        (StageLift.printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r++[])) by omega))

/-- `prop:time`, paper/paper.tex: the physical
outer frame multiplies the existing complete source clock by at most
a fixed factor, so its raw-index charge remains additive once. -/
theorem framedSourceBudget_le {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    framedSourceBudget r≤5*StageLift.sourceMachineBudget r := by
  let K:=StageCert.Tokens.structuralSourceCallee B1 B2
  let z:=StageLift.printSourceSizes B1 B2
  let bits:=Greedy.printInput r
  let A:=500*(z.W (leadOnes bits)+1)^2+100*(TSK K+3)+5+MM*5*(2*z.W (leadOnes bits)+1)
  have hlinear : ∀ n,langBudget K z VV MM bits n=langBudget K z VV MM bits 0+n*A := by
    intro n
    unfold langBudget
    dsimp only [A]
    ring
  have hn : 1≤StageLift.sourceProgramSteps r := by
    change 1≤(StageLift.carrierStartupCost r+6+
      StageLift.allWalkSourceCost r
        (StageLift.printSourceContext B1 B2 (Greedy.printInput r)).Lk
        (StageLift.printSourceContext B1 B2 (Greedy.printInput r)).Bk)+1
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hs : 3*StageLift.sourceProgramSteps r+2≤5*StageLift.sourceProgramSteps r := by omega
  have hm:=Nat.mul_le_mul_right A hs
  change langBudget K z VV MM bits (3*StageLift.sourceProgramSteps r+2)≤
    5*langBudget K z VV MM bits (StageLift.sourceProgramSteps r)
  rw [hlinear (3*StageLift.sourceProgramSteps r+2),hlinear (StageLift.sourceProgramSteps r)]
  nlinarith

end NearQuarticWires.StageCompiledTerms
