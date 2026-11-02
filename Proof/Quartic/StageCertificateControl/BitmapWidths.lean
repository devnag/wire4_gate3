import Proof.Quartic.StageCertificateControl.CountStartCost
import Proof.Quartic.StageCertificateControl.BitmapProgram
import Proof.Quartic.StageCertificateControl.PublicBounds

/-!
# Original-arity arithmetic widths for the native bitmap consumer

Paper: `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the bitmap
arithmetic width is a fixed original-arity polynomial. It reserves no
native-table or callee budget and does not inspect the native suffix. -/
def bitmapSizes (B1 B2 coefficient degree : ℕ) : Sz :=
  ⟨(StageCertTests.prepScheduleSizes B1 B2).a1+coefficient+10,
    StageCertTests.prepScheduleDegree B1 B2+degree+2,0,0,0,0⟩

/-- `prop:time`, paper/paper.tex: increasing
only the scalar polynomial width preserves all earlier parameter-reader
reserves on the same actual word. -/
theorem bitmap_context_dominates (B1 B2 coefficient degree : ℕ) (word : List Bool) :
    (ctxOf StageRecovery.packetCallee (StageCertTests.prepScheduleSizes B1 B2) word).Wd≤
      (ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) word).Wd := by
  change 2^((StageCertTests.prepScheduleSizes B1 B2).c1*leadOnes word)*
      (StageCertTests.prepScheduleSizes B1 B2).a1≤
    2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*leadOnes word)*
      ((StageCertTests.prepScheduleSizes B1 B2).a1+coefficient+10)
  apply Nat.mul_le_mul
  · apply Nat.pow_le_pow_right (by decide)
    change StageCertTests.prepScheduleDegree B1 B2*leadOnes word≤_
    exact Nat.mul_le_mul_right _ (by omega)
  · omega

/-- `sec:params` and `prop:time`, paper/paper.tex: dispatch supplies the full original call and parameter
parser guards even when arbitrary native bytes follow the preparation. -/
theorem bitmap_context_public {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c=some p) (coefficient degree : ℕ) (suffix : List Bool) :
    let C := ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree)
      (true::(callWord c++suffix))
    (callWord c).length+2≤C.Wd ∧ 64*(StageCertTests.scheduleHint p.1+1)≤C.Wd := by
  have h := StageCertTests.prepSchedule_context_widths hd suffix
  have hm := bitmap_context_dominates B1 B2 coefficient degree (true::(callWord c++suffix))
  exact ⟨h.1.trans hm,h.2.trans hm⟩

/-- `prop:time`, paper/paper.tex: the true
original arity header supplies a numeric reserve for every native record
width in a fixed polynomial envelope, independently of table size. -/
theorem bitmap_context_arity (B1 B2 coefficient degree : ℕ) (c : Call) (suffix : List Bool) :
    (coefficient+10)*(c.n+1)^(degree+2)≤
      (ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree)
        (true::(callWord c++suffix))).Wd := by
  have hn : c.n+1≤2^natBitLength c.n := lt_natBitLength c.n
  have hp : (c.n+1)^(degree+2)≤
      2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*(1+natBitLength c.n)) := by
    calc
      (c.n+1)^(degree+2)≤(2^natBitLength c.n)^(degree+2) := Nat.pow_le_pow_left hn _
      _ = 2^(natBitLength c.n*(degree+2)) := by rw [Nat.pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  change (coefficient+10)*(c.n+1)^(degree+2)≤
    2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*leadOnes (true::(callWord c++suffix)))*
      ((StageCertTests.prepScheduleSizes B1 B2).a1+coefficient+10)
  rw [StageMain.taggedCall_header_width]
  calc
    _ ≤ (coefficient+10)*2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*(1+natBitLength c.n)) :=
      Nat.mul_le_mul_left _ hp
    _ = 2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*(1+natBitLength c.n))*(coefficient+10) :=
      Nat.mul_comm _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

/-- `prop:time`, paper/paper.tex: native-width
guards and original-center exponentiation share one original-arity
reserve, with no census-sized arithmetic width. -/
theorem bitmap_context_reserve (B1 B2 coefficient degree : ℕ) (c : Call) (suffix : List Bool) :
    coefficient*(c.n+1)^degree+c.n+4≤
      (ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree)
        (true::(callWord c++suffix))).Wd := by
  have h := bitmap_context_arity B1 B2 coefficient degree c suffix
  have hn : 1≤c.n+1 := by omega
  have hp := Nat.pow_le_pow_right hn (by omega : degree≤degree+2)
  have hnp := Nat.pow_le_pow_right hn (by omega : 1≤degree+2)
  simp only [pow_one] at hnp
  have hm := Nat.mul_le_mul_left coefficient hp
  nlinarith

/-- `sec:params`, paper/paper.tex: the default branch
has a fixed positive scalar reserve on every word, including false tags. -/
theorem bitmap_context_width (B1 B2 coefficient degree : ℕ) (word : List Bool) :
    2≤(ctxOf StageRecovery.packetCallee (bitmapSizes B1 B2 coefficient degree) word).Wd := by
  have hp : 1≤2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*leadOnes word) :=
    Nat.one_le_pow _ _ (by decide)
  change 2≤2^((StageCertTests.prepScheduleDegree B1 B2+degree+2)*leadOnes word)*
    ((StageCertTests.prepScheduleSizes B1 B2).a1+coefficient+10)
  nlinarith

end NearQuarticWires.StageCertificateControl
