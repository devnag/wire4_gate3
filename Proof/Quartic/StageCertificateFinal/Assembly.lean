import Proof.Quartic.StageCertificateFinal.Ledger
import Proof.Quartic.Program.Final

/-!
# The complete certificate field from its generated native tables

Paper: `thm:counter`, paper/paper.tex,
Step 2 of `sec:algorithm`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `thm:counter`, `sec:algorithm` and `prop:time`,
paper/paper.tex:
complete generated native tables with their physical word function
instantiate the exact certificate field. Its count, strict signed
tests, original-column meaning, default, retained preparation and
all-calls runtime ledger are all proved by the composed program. -/
noncomputable def certFieldOfTables {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (tablePayload tables r)) baseBudget)
    (baseEnvelope : Call→List Bool→ℕ)
    (hbase : ∀r : IndexedRequest B1 B2,baseBudget r≤baseEnvelope r.prepared.call r.prepared.witness)
    (hledger : Program.LedgerCost B1 B2 baseEnvelope) : Program.CertField B1 B2 where
  certBudget := retainedBudget tables baseBudget
  cert := retainedCertificateWordFunction tables base
  certCost := retainedBudget_ledger tables base baseEnvelope hbase hledger

/-- `prop:time` and `thm:counter`, paper/paper.tex: the actual whole-table budget bound
supplies the original-call ledger directly, so no separate envelope
or runtime hypothesis is needed beyond that proved native bound. -/
noncomputable def certFieldOfBudgetBound {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (tablePayload tables r)) baseBudget)
    (hbound : ∃K e : ℕ,∀r : IndexedRequest B1 B2,
      baseBudget r≤K*((callWord r.prepared.call).length+1)^e+
        K*Program.runEnvelope B1 B2 e r.prepared.call) : Program.CertField B1 B2 := by
  classical
  let K := Classical.choose hbound
  let e := Classical.choose (Classical.choose_spec hbound)
  have hb := Classical.choose_spec (Classical.choose_spec hbound)
  exact certFieldOfTables tables base
    (fun c _ => K*((callWord c).length+1)^e+K*Program.runEnvelope B1 B2 e c)
    hb ⟨K,e,fun _ _ => le_rfl⟩

end NearQuarticWires.StageCertificateFinal
