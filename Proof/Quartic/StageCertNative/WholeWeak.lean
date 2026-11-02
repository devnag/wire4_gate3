import Proof.Quartic.StageCertNative.PayloadBatch

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open StageCertificateControl

section
variable {B1 B2 : ℕ} {termBudget : TermJob B1 B2→ℕ}
variable (termProducer : WordFunction (TermJob B1 B2) TermJob.word
  (fun r=>frame (termWeakWord r)) termBudget)

noncomputable def wholeWeakOnlyBudget (r : IndexedRequest B1 B2) : ℕ :=
  2*payloadBatchCost (termFamily r) termWeakWord termBudget (cachedCountBudget r)+2

/-- `lem:print`, paper/paper.tex: every actual
term is evaluated at the original cached source; the output contains
only the concatenated signed cut payload, with no preparation suffix. -/
noncomputable def wholeWeakOnlyWordFunction :
    WordFunction (IndexedRequest B1 B2) cachedSourceWord
      (fun r=>frame (wholeWeakWord r)) (wholeWeakOnlyBudget (termBudget:=termBudget)) := by
  let counter:=cachedCountWordFunction B1 B2
  let provider:=extendedBankWordFunction termProducer counter.program.tapeCount
  have hq : counter.program.tapeCount≤provider.program.tapeCount := by
    change counter.program.tapeCount≤termProducer.program.tapeCount+counter.program.tapeCount
    omega
  let f:=payloadBatchWordFunction counter provider hq termFamily (fun _=>rfl) (fun _=>rfl)
  refine ⟨f.program,?_⟩
  intro r
  have ho : (List.range (termFamily r).count).flatMap ((termFamily r).caches termWeakWord)=
      wholeWeakWord r := (wholeWeakWord_eq_range r).symm
  simpa only [ho,wholeWeakOnlyBudget] using f.realizes r

noncomputable def wholeWeakOriginalBudget (r : IndexedRequest B1 B2) : ℕ :=
  4*cachedSourceBudget r+4*wholeWeakOnlyBudget (termBudget:=termBudget) r+12

/-- `lem:print` and `prop:time`, paper/paper.tex: BASE alone constructs the actual whole-test signed
cut stream, including all original N² population or N⁸ closed-walk
terms and the complete source, count, context and final scan costs. -/
noncomputable def wholeWeakOriginalWordFunction :
    WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r=>frame (wholeWeakWord r)) (wholeWeakOriginalBudget (termBudget:=termBudget)) :=
  Program.WordFunction.pipe (cachedSourceWordFunction B1 B2) (wholeWeakOnlyWordFunction termProducer)

end

end NearQuarticWires.StageCertNative
