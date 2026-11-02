import Proof.Quartic.StageCertificateFinal.RetainedMachine
import Proof.Quartic.StageCertificateControl.CertificateBatchLedger
import Proof.Quartic.StageCert.CallLedger

/-!
# The complete certificate-stage physical budget has the declared ledger

Paper: `prop:time`, paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `prop:time`, paper/paper.tex: a fixed
scalar cost is polynomial in the original call-word length. -/
theorem constant_poly (n : ℕ) : Program.PolyCost (fun (_ : Call) (_ : List Bool) => n) :=
  ⟨n,0,by intros;simp⟩

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the sole appended certificate frame has
two bits per original column and one delimiter; defaults append none. -/
theorem certificateSuffix_length (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    (certificateSuffix B1 B2 c w).length≤2*StageCert.actualColumnCount B1 B2 c+1 := by
  cases hd : Program.dispatch B1 B2 c with
  | none => simp only [certificateSuffix,StageCert.actualColumnCount,hd,List.length_nil,Nat.zero_le]
  | some p =>
    have hl : (Program.certifiedBits (Program.runCall c p w)).length=2^(c.n-p.1.k) := by
      rw [Program.certifiedBits,List.length_ofFn]
      rfl
    simp only [certificateSuffix,StageCert.actualColumnCount,hd,
      NearCubicGates.Close.Codec.frame_eq_marks,List.length_append,
      Streaming.marks_length,List.length_singleton,hl,le_refl]

/-- `prop:time`, paper/paper.tex:
the literal suffix bytes have the original all-calls ledger, without
charging an arbitrary witness suffix or an intermediate table crop. -/
theorem certificateSuffix_length_ledger (B1 B2 : ℕ) :
    Program.LedgerCost B1 B2 (fun c w => (certificateSuffix B1 B2 c w).length) := by
  exact StageCert.ledger_mono
    (Greedy.LedgerCost.add
      (Greedy.LedgerCost.mul_poly (constant_poly 2) (StageCert.actualColumnCount_ledger B1 B2))
      (Greedy.LedgerCost.of_poly (constant_poly 1))) (certificateSuffix_length B1 B2)

/-- `prop:time`, paper/paper.tex:
the actual sequential native-batch and bitmap compiler budget has one
total all-calls ledger; every complete native table is paid in full. -/
theorem suffixBudget_ledger {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (tablePayload tables r)) baseBudget)
    (baseEnvelope : Call→List Bool→ℕ)
    (hbase : ∀r : IndexedRequest B1 B2,baseBudget r≤baseEnvelope r.prepared.call r.prepared.witness)
    (hledger : Program.LedgerCost B1 B2 baseEnvelope) :
    Program.LedgerCost B1 B2 (fun c w => suffixBudget tables baseBudget (c,w)) := by
  exact Greedy.LedgerCost.add
    (Greedy.LedgerCost.add
      (Greedy.LedgerCost.mul_poly (constant_poly 4)
        (certificateBatchBudget_ledger B1 B2 base baseEnvelope hbase hledger))
      (Greedy.LedgerCost.mul_poly (constant_poly 4) (bitmapBudget_ledger tables)))
    (Greedy.LedgerCost.of_poly (constant_poly 12))

/-- `prop:time`, paper/paper.tex:
the actual complete retained certificate program has the declared
counter ledger, including all tables, bitmap work, both payload copies,
compiler setup and teardown, on every original call and witness. -/
theorem retainedBudget_ledger {B1 B2 : ℕ} (tables : NativeTables B1 B2)
    {baseBudget : IndexedRequest B1 B2→ℕ}
    (base : WordFunction (IndexedRequest B1 B2) IndexedRequest.baseWord
      (fun r => frame (tablePayload tables r)) baseBudget)
    (baseEnvelope : Call→List Bool→ℕ)
    (hbase : ∀r : IndexedRequest B1 B2,baseBudget r≤baseEnvelope r.prepared.call r.prepared.witness)
    (hledger : Program.LedgerCost B1 B2 baseEnvelope) :
    Program.LedgerCost B1 B2 (retainedBudget tables baseBudget) := by
  have hp : Program.PolyCost (fun c w => (Program.prepWord B1 B2 c w).length) :=
    ⟨200*(Cells.ParameterArithmetic.preparationCoefficient B1+5),B1+12,
      Cells.all_calls_prepWord_length B1 B2⟩
  have hb := Greedy.LedgerCost.add
    (Greedy.LedgerCost.add (Greedy.LedgerCost.of_poly hp)
      (certificateSuffix_length_ledger B1 B2)) (Greedy.LedgerCost.of_poly (constant_poly 1))
  exact Greedy.LedgerCost.add
    (Greedy.LedgerCost.mul_poly (constant_poly 2)
      (Greedy.LedgerCost.add
        (Greedy.LedgerCost.mul_poly (constant_poly 2)
          (suffixBudget_ledger tables base baseEnvelope hbase hledger))
        (Greedy.LedgerCost.mul_poly (constant_poly 150) hb)))
    (Greedy.LedgerCost.of_poly (constant_poly 2))

end NearQuarticWires.StageCertificateFinal
