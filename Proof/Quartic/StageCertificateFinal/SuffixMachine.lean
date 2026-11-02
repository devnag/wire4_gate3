import Proof.Quartic.StageCertificateFinal.Stream
import Proof.Quartic.StageCertificateFinal.Meaning
import Proof.Quartic.Program.Pipe

/-!
# The complete native batch followed by the sole final certificate crop

Paper: `lem:print`, paper/paper.tex,
Step 2 of `sec:algorithm`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: the
literal sequential compiler charges the entire native batch and
the actual cold bitmap consumer with its physical composition cost. -/
noncomputable def suffixBudget {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    (baseBudget : IndexedRequest B1 B2→ℕ) (r : Call×List Bool) : ℕ :=
  4*certificateBatchBudget B1 B2 (tablePayload tables) baseBudget r+
    4*(bitmapRequest tables r.1 r.2).budget+12

/-- `sec:algorithm`, `lem:print` and `prop:time`,
paper/paper.tex:
one fixed physical program computes every complete native table,
conjoins all padded signed values, and emits the literal certificate
suffix after its sole final original-center crop. -/
noncomputable def suffixWordFunction {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (tablePayload tables r)) baseBudget) :
    WordFunction (Call×List Bool) (fun r => Program.prepWord B1 B2 r.1 r.2)
      (fun r => frame (certificateSuffix B1 B2 r.1 r.2)) (suffixBudget tables baseBudget) := by
  let batch := certificateBatchWordFunction B1 B2 base
  let batch' : WordFunction (Call×List Bool) (fun r => Program.prepWord B1 B2 r.1 r.2)
      (fun r => frame (bitmapRequest tables r.1 r.2).word)
      (certificateBatchBudget B1 B2 (tablePayload tables) baseBudget) :=
    { program := batch.program
      realizes := fun r => by
        rcases r with ⟨c,w⟩
        simpa only [batch_eq_bitmapWord,countWord] using batch.realizes (c,w) }
  let combined := Program.WordFunction.pipe batch' (bitmapMachine tables)
  exact
    { program := combined.program
      realizes := fun r => by simpa only [bitmap_output,suffixBudget] using combined.realizes r }

end NearQuarticWires.StageCertificateFinal
