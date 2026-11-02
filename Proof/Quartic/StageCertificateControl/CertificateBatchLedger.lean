import Proof.Quartic.StageCertificateControl.CertificateBatch
import Proof.Quartic.StageCertificateControl.BatchedLedger

/-!
# The actual all-calls certificate table batch satisfies its runtime ledger

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex:
the actual native base budget, original-call polynomial indexing and
threshold retention, physical count bootstrap, all complete table
calls, output copies and final flattening satisfy one total all-calls
ledger. The native budget is charged once per actual test and retains
only polynomial original-source multipliers. -/
theorem certificateBatchBudget_ledger (B1 B2 : ℕ)
    {payload : IndexedRequest B1 B2→List Bool} {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (payload r)) baseBudget)
    (baseEnvelope : Call→List Bool→ℕ)
    (hbase : ∀r : IndexedRequest B1 B2,baseBudget r≤baseEnvelope r.prepared.call r.prepared.witness)
    (hledger : Program.LedgerCost B1 B2 baseEnvelope) :
    Program.LedgerCost B1 B2 (fun c w => certificateBatchBudget B1 B2 payload baseBudget (c,w)) := by
  obtain ⟨K,e,hK⟩ := indexedNativeBudget_linear B1 B2 baseBudget
  let nativeBudget (c : Call) (w : List Bool) :=
    80008*baseEnvelope c w+K*((callWord c).length+1)^e
  have hconstant : Program.PolyCost (fun (_ : Call) (_ : List Bool) => 80008) :=
    ⟨80008,0,fun _ _ => by simp⟩
  have hpoly : Program.PolyCost (fun (c : Call) (_ : List Bool) => K*((callWord c).length+1)^e) :=
    ⟨K,e,fun _ _ => le_rfl⟩
  have hn : Program.LedgerCost B1 B2 nativeBudget :=
    Greedy.LedgerCost.add (Greedy.LedgerCost.mul_poly hconstant hledger) (Greedy.LedgerCost.of_poly hpoly)
  have hbound (c : Call) (w : List Bool) (j : Fin (certificatePoolFamily B1 B2 (c,w)).count) :
      indexedNativeBudget baseBudget ((certificatePoolFamily B1 B2 (c,w)).request j)≤nativeBudget c w := by
    let r := (certificatePoolFamily B1 B2 (c,w)).request j
    have h := hK r
    have hb := hbase r
    obtain ⟨hc,hw⟩ := certificatePoolFamily_request B1 B2 (c,w) j
    change r.prepared.call=c at hc
    change r.prepared.witness=w at hw
    rw [hc,hw] at hb
    rw [hc] at h
    change indexedNativeBudget baseBudget r≤nativeBudget c w
    dsimp [nativeBudget]
    omega
  exact batchedMachine_ledger B1 B2 (indexedNativeWordFunction B1 B2 base)
    (fun c w => certificatePoolFamily B1 B2 (c,w))
    (fun c w => certificatePoolFamily_source B1 B2 (c,w))
    (fun c w => certificatePoolFamily_count B1 B2 (c,w)) nativeBudget hbound hn

end NearQuarticWires.StageCertificateControl
