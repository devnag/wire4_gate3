import Proof.Quartic.StageCertNative.WholeWeak
import Proof.Quartic.StageCertNative.HeaderData

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl

section
variable {B1 B2 : ℕ} {termBudget : TermJob B1 B2→ℕ}
variable (termProducer : WordFunction (TermJob B1 B2) TermJob.word
  (fun r=>frame (termWeakWord r)) termBudget)

noncomputable def nativeInputBudget (r : IndexedRequest B1 B2) : ℕ :=
  2*StageRecovery.FramedPair.cost (input:=IndexedRequest.baseWord)
    (left:=nativeFieldsWord) (right:=wholeWeakWord)
    (lb:=nativeFieldsBudget) (rb:=wholeWeakOriginalBudget (termBudget:=termBudget)) r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: the original BASE source constructs exactly the five
actual native scalars and every original term's signed weak cuts,
with one final concatenation and no supplied native table or header. -/
noncomputable def nativeInputWordFunctionOf :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (nativeHeaderRequest r).word) (nativeInputBudget (termBudget:=termBudget)) := by
  let f:=StageRecovery.FramedPair.wordFunction (nativeFieldsWordFunction B1 B2)
    (wholeWeakOriginalWordFunction termProducer)
  refine ⟨f.program,?_⟩
  intro r
  have hw:=nativeHeaderRequest_word r
  simpa only [←hw,nativeInputBudget] using f.realizes r

end

end NearQuarticWires.StageCertNative
