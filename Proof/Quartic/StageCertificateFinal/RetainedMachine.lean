import Proof.Quartic.StageCertificateFinal.SuffixMachine
import Proof.Quartic.StageGamma.Retain

/-!
# The complete certificate stage preserves its original preparation

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: the
actual retained-input compiler budget includes its complete once-only
certificate computation and both physical payload-copy passes. -/
noncomputable def retainedBudget {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    (baseBudget : IndexedRequest B1 B2→ℕ) (c : Call) (w : List Bool) : ℕ :=
  2*(2*suffixBudget tables baseBudget (c,w)+
    150*((Program.prepWord B1 B2 c w).length+(certificateSuffix B1 B2 c w).length+1))+2

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the actual certificate computation preserves
the original preparation once and appends its literal certificate
frame; closed and rejected calls append an empty suffix. -/
noncomputable def retainedCertificateWordFunction {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (tablePayload tables r)) baseBudget) :
    WordFunction (Call×List Bool) (fun r => Program.prepWord B1 B2 r.1 r.2)
      (fun r => frame (Program.certWord B1 B2 r.1 r.2))
      (fun r => retainedBudget tables baseBudget r.1 r.2) := by
  let retained := StageGamma.retainedWordFunction (suffixWordFunction tables base)
  exact
    { program := retained.program
      realizes := fun r => by
        rcases r with ⟨c,w⟩
        simpa only [retainedBudget,StageGamma.retainedCost,←certWord_eq_prep_append]
          using retained.realizes (c,w) }

end NearQuarticWires.StageCertificateFinal
