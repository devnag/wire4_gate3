import Proof.Quartic.StageCertificateFinal.Thresholds
import Proof.Quartic.StageCertificateControl.BitmapMachine
import Proof.Quartic.StageCertificateControl.BitmapLedger

/-!
# The actual complete generated native batch is a cold bitmap request

Paper: `lem:print`, paper/paper.tex,
Step 2 of `sec:algorithm`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertificateControl

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: complete actual native table data instantiate
every count, width, signed-fit and threshold field of the physical
bitmap request, on all calls and all witnesses before filtering. -/
noncomputable def bitmapRequest {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool) :
    BitmapRequest B1 B2 tables.coefficient tables.degree where
  call := c
  witness := w
  tests := tests tables c w
  count_eq := tests_count tables c w
  lengths := fun p _ => tests_lengths tables c w p
  values_fit := tests_values_fit tables c w
  widths := tests_widths tables c w
  threshold_bits := fun p _ => tests_threshold_bits tables c w p

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the actual complete generated batch is
consumed by the existing physical cold bitmap machine, with every
padded native value tested before the single final crop. -/
noncomputable def bitmapMachine {B1 B2 : ℕ} (tables : NativeTables B1 B2) :
    WordFunction (Call×List Bool) (fun r => (bitmapRequest tables r.1 r.2).word)
      (fun r => (bitmapRequest tables r.1 r.2).output)
      (fun r => (bitmapRequest tables r.1 r.2).budget) where
  program := (bitmapWordFunction B1 B2 tables.coefficient tables.degree).program
  realizes r := (bitmapWordFunction B1 B2 tables.coefficient tables.degree).realizes (bitmapRequest tables r.1 r.2)

/-- `prop:time`, paper/paper.tex:
the actual bitmap compilation budget for the complete generated batch
satisfies the original all-calls counter ledger, without a hypothesis
that any witness or native column is certified. -/
theorem bitmapBudget_ledger {B1 B2 : ℕ} (tables : NativeTables B1 B2) :
    Program.LedgerCost B1 B2 (fun c w => (bitmapRequest tables c w).budget) :=
  StageCertificateControl.bitmapBudget_ledger (bitmapRequest tables) (by intro c w;rfl)

end NearQuarticWires.StageCertificateFinal
