import Proof.Quartic.StageCertificateFinal.Tests
import Proof.Quartic.StageCertificateControl.PublicBounds

/-!
# Actual strict thresholds have the original parameter-word bit bound

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Cells
open StageCertificateControl

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: the literal selected threshold
has the original scheduler bit bound, independently of every witness
and before any native-column certificate has been established. -/
theorem request_threshold_bits {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    natBitLength r.metadata.threshold≤StageCertTests.scheduleHint r.prepared.selected.1 := by
  let C := ctxOf StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2) r.prepared.word
  have hw : 64*(StageCertTests.scheduleHint r.prepared.selected.1+1)≤C.Wd := r.prepared.widths.2
  have hm := congrArg StageCertTests.TestMetadata.threshold (StageCertNative.actualOrdinal_metadata r)
  rw [←hm,StageCertTests.TestOrdinal.metadata_threshold]
  exact actualTestThreshold_binary_bound C r.prepared.selected.1 hw (StageCertNative.actualOrdinal r).kind

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: every physically visited test's
threshold is bounded by the same original selected parameter record. -/
theorem tests_threshold_bits {B1 B2 : ℕ} (tables : NativeTables B1 B2) (c : Call) (w : List Bool)
    (p : Program.Selected c) :
    ∀test∈tests tables c w,natBitLength test.bound≤StageCertTests.scheduleHint p.1 := by
  intro test ht
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ht
  let r := (certificatePoolFamily B1 B2 (c,w)).request j
  have hp := family_parameters_eq B1 B2 c w j p
  change r.prepared.selected.1=p.1 at hp
  change natBitLength r.metadata.threshold≤_
  simpa only [hp] using request_threshold_bits r

end NearQuarticWires.StageCertificateFinal
