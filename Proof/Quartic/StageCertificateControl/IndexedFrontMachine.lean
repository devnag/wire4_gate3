import Proof.Quartic.StageCertificateControl.IndexedExecution
import Proof.Gates.Expand.PolyTabPack

/-!
# The actual cold whole-test indexing word function

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Interfaces
open StageCertTests

/-- `prop:time`, paper/paper.tex: the
complete indexing machine pays its actual source execution and final
parallel return of every physical head. -/
noncomputable def indexedFrontBudget {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  2*indexedFrontSourceSteps r+2

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: one fixed physical machine derives the exact
threshold header and selected complete five-field request directly
from the indexed original preparation. The actual scheduler, every
binary copy, all work tapes, and final head returns are included. -/
noncomputable def indexedFrontWordFunction (B1 B2 : ℕ) :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.word
      (fun r => frame r.frontWord) indexedFrontBudget :=
  wordFunction_of_ideal (indexedFrontProgram (framedScheduleWordFunction B1 B2).program)
    (indexedFinal (framedScheduleWordFunction B1 B2).program) (by simp [indexedFinal])
    indexedFrontSourceSteps (fun _ _ => 0) indexedFrontSourceSteps
    (by intro r;exact Nat.le_refl _)
    (by intro r;exact ⟨rfl,indexedFront_exec r⟩)

/-- `prop:time`, paper/paper.tex: the
actual cold indexing budget is uniformly polynomial in the original
call word, over every witness and every valid scheduled test index. -/
theorem indexedFrontBudget_polynomial (B1 B2 : ℕ) :
    ∃ K e : ℕ, ∀ r : IndexedRequest B1 B2,
      indexedFrontBudget r≤K*((callWord r.prepared.call).length+1)^e := by
  have hp := ((PreparedPolynomial.const (2*10000000)).mul
    ((indexedSourceMass_polynomial B1 B2).pow 2)).add (PreparedPolynomial.const 2)
  obtain ⟨K,e,hK⟩ := hp
  refine ⟨K,e,fun r => ?_⟩
  simpa only [indexedFrontBudget,indexedFrontSourceSteps,Nat.mul_assoc] using hK r.prepared

end NearQuarticWires.StageCertificateControl
