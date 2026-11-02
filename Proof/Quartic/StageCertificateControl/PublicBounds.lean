import Proof.Quartic.StageCertificateControl.CertificateMeaning
import Proof.Quartic.StageCertTests.ScheduleCount
import Proof.Quartic.StageCertTests.ScheduleSemantics
import Proof.Quartic.StageCertTests.ScheduleBounds

/-!
# Public bounds of the exact whole-test plan

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
Step 2 of `sec:algorithm`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- The physical whole-test count of `sec:algorithm`,
paper/paper.tex, is exactly the literal column-certificate
plan count on the selected positive chain. -/
theorem actualTestPlan_length_metadata (c : Call) (p : Cells.Parameters) (hJ : 1≤p.J) :
    (StageCertTests.actualTestPlan c p).length=(StageCertTests.certificateMetadata p c.kind).length := by
  have hk := congrArg List.length (StageCertTests.ordinalTestPlan_kind (p.J-1) (Builder.circuitSet c))
  have hm := congrArg List.length (StageCertTests.certificateMetadata_eq_ordinalTestPlan c p hJ)
  simp only [List.length_map] at hk hm
  exact hk.symm.trans hm.symm

/-- The real test census of `sec:algorithm` and `prop:time`,
paper/paper.tex, fits both the
count register and its actual header decoder using only the public
unpowered parameter-word width. -/
theorem metadata_count_binary_bounds (C : Ctx) (p : Cells.Parameters) (kind : CallKind)
    (hW : 64*(StageCertTests.scheduleHint p+1)≤C.Wd) :
    natBitLength (StageCertTests.certificateMetadata p kind).length+2≤C.Wd ∧
      (StageCertTests.certificateMetadata p kind).length<2^C.Wd := by
  let B := StageCertTests.scheduleHint p
  have bounds := StageCertTests.scheduleBounds_of_width C p hW
  have hJ : p.J+1≤2^B := (lt_natBitLength p.J).trans_le
    (Nat.pow_le_pow_right (by decide) bounds.chainBits)
  have hcc := StageCertTests.callCircuitCount_bounds kind
  have hmul := Nat.mul_le_mul hcc.2 (Nat.mul_le_mul_left 128 hJ)
  have hpow : 1≤2^B := Nat.one_le_pow _ _ (by decide)
  have ht : (StageCertTests.certificateMetadata p kind).length<2^(B+9) := by
    rw [StageCertTests.certificateMetadata_length,pow_add]
    norm_num
    nlinarith
  have hbits := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega : 1≤B+9) ht
  have hBW : B+11≤C.Wd := by change 64*(B+1)≤C.Wd at hW;omega
  exact ⟨by omega,ht.trans_le (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- Every literal strict-test threshold of `eq:testX`–`eq:testPhi`,
paper/paper.tex, has binary length controlled by
the public parameter-word header, before any certification premise. -/
theorem actualTestThreshold_binary_bound (C : Ctx) (p : Cells.Parameters)
    (hW : 64*(StageCertTests.scheduleHint p+1)≤C.Wd)
    (kind : StageCertTests.TestKind (p.J-1)) :
    natBitLength (StageCertTests.actualTestThreshold p kind)≤StageCertTests.scheduleHint p := by
  have bounds := StageCertTests.scheduleBounds_of_width C p hW
  cases kind with
  | population =>
    simpa [StageCertTests.actualTestThreshold,StageCertTests.ThresholdKind.threshold,
      StageCertTests.ThresholdKind.field,StageCertTests.ThresholdKind.increment,
      StageCertTests.ThresholdKind.multiplier,StageCertTests.ScheduleField.value,Nat.mul_comm]
      using bounds.powerBits .population
  | digit j pattern position =>
    simpa [StageCertTests.actualTestThreshold,StageCertTests.ThresholdKind.threshold,
      StageCertTests.ThresholdKind.field,StageCertTests.ThresholdKind.increment,
      StageCertTests.ThresholdKind.multiplier,StageCertTests.ScheduleField.value,Nat.mul_comm]
      using bounds.powerBits .digit
  | finalError j pattern =>
    simpa [StageCertTests.actualTestThreshold,StageCertTests.ThresholdKind.threshold,
      StageCertTests.ThresholdKind.field,StageCertTests.ThresholdKind.increment,
      StageCertTests.ThresholdKind.multiplier,StageCertTests.ScheduleField.value,Nat.mul_comm]
      using bounds.powerBits .finalError

end NearQuarticWires.StageCertificateControl
