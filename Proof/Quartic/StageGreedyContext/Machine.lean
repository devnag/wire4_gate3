import Proof.Quartic.StageGreedyContext.Body

/-!
# The actual complete one-context ordinary word function

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab

attribute [local irreducible] setup

/-- `lem:print`, paper/paper.tex: the
fresh final output is distinct from the original carrier tape. -/
theorem output_not_zero (p : Program) : (2 : Fin (p.tapeCount+4)).val≠0 := by
  change 2%(p.tapeCount+4)≠0
  rw [Nat.mod_eq_of_lt (by omega)]
  decide

/-- `lem:print`, paper/paper.tex: the
fresh final output is outside the sole context-call reset ruler. -/
theorem output_off_ruler (p : Program) : (2 : Fin (p.tapeCount+4))≠ruler p := by
  intro h
  have hh:=congrArg Fin.val h
  change 2%(p.tapeCount+4)=3 at hh
  rw [Nat.mod_eq_of_lt (by omega)] at hh
  omega

/-- `prop:time`, paper/paper.tex: the
actual ordinary compiler budget includes the complete frontend
source execution and its final physical head restoration. -/
noncomputable def Request.budget {B1 B2 : ℕ} (r : Request B1 B2) : ℕ :=
  2*r.sourceSteps+2

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual ordinary program reads
the original carrier, computes the common context once, preserves
all count and entry bytes, and prints the exact nested-context frame. -/
noncomputable def requestWordFunction (B1 B2 : ℕ) :
    WordFunction (Request B1 B2) Request.word Request.output Request.budget :=
  wordFunction_of_ideal (contextBody B1 B2) 2 (output_not_zero (setup B1 B2).program)
    Request.capacity Request.blankLengths Request.sourceSteps (fun _=>le_rfl) (by
      intro r
      refine ⟨?_,contextBody_run r⟩
      change (if (2 : Fin ((setup B1 B2).program.tapeCount+4))=ruler (setup B1 B2).program
        then r.setupBudget else 0)=0
      rw [if_neg (output_off_ruler (setup B1 B2).program)])

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: the complete actual
frontend at the frozen carrier interface has no source, context,
table or execution supplier premise. Its sole subroutine is the
actual common-context source program. -/
noncomputable def contextProducer (B1 B2 : ℕ) : StageGreedyCollector.ContextProducer B1 B2 :=
  ⟨fun r=>(actualRequest r).budget,
    { program:=(requestWordFunction B1 B2).program
      realizes:=fun r=>by
        simpa only [actualRequest_word,actualRequest_output]
          using (requestWordFunction B1 B2).realizes (actualRequest r) }⟩

end NearQuarticWires.StageGreedyContext
