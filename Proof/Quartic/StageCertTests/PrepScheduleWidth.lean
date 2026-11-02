import Proof.Quartic.StageCertTests.SchedulePublicBounds
import Proof.Quartic.StageRecovery.PacketRequest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex:
the direct preparation-source scheduler uses a fixed polynomial
arity exponent depending only on the public normalization constants. -/
def prepScheduleDegree (B1 B2 : ℕ) : ℕ :=
  (B2+8)*(2*(B1+12))+(B2+8)

/-- `prop:time`, paper/paper.tex:
the actual direct-source workspace reserves no native table or callee;
only arithmetic width is allocated from the original arity header. -/
def prepScheduleSizes (B1 B2 : ℕ) : Sz :=
  ⟨128*(scheduleWidthCoefficient B1*1002^(2*(B1+12))+1004),prepScheduleDegree B1 B2,0,0,0,0⟩

/-- `sec:params` and `prop:time`, paper/paper.tex: the literal true-tagged arity header supplies both
the complete original-call reader width and every actual selected
scheduler bound, independently of witness and later table suffixes. -/
theorem prepSchedule_context_widths {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) (suffix : List Bool) :
    let C := ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2) (true :: (callWord c ++ suffix))
    (callWord c).length+2 ≤ C.Wd ∧ 64*(scheduleHint p.1+1) ≤ C.Wd := by
  let A := scheduleWidthCoefficient B1*1002^(2*(B1+12))
  let D := prepScheduleDegree B1 B2
  let K := 128*(A+1004)
  let Y := (c.n+1)^D
  have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by omega)
  have hdegree : (B2+8)*(2*(B1+12)) ≤ D := by dsimp [D,prepScheduleDegree];omega
  have hcallDegree : B2+8 ≤ D := by dsimp [D,prepScheduleDegree];omega
  have hh0 := dispatched_scheduleHint_arity hd
  have hh : scheduleHint p.1 ≤ A*Y := hh0.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdegree))
  have hc0 := StageMain.CallSize.dispatched_callWord_polynomial hd
  have hc : (callWord c).length ≤ 1001*Y := hc0.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hcallDegree))
  have hreq : 64*(scheduleHint p.1+1)+(callWord c).length+2 ≤ K*Y := by
    dsimp only [K]
    nlinarith
  have hn : c.n+1 ≤ 2^natBitLength c.n := lt_natBitLength c.n
  have hypow : Y ≤ 2^(D*(1+natBitLength c.n)) := by
    calc
      Y ≤ (2^natBitLength c.n)^D := Nat.pow_le_pow_left hn D
      _ = 2^(natBitLength c.n*D) := by rw [Nat.pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hbound : 64*(scheduleHint p.1+1)+(callWord c).length+2 ≤
      (ctxOf StageRecovery.packetCallee (prepScheduleSizes B1 B2)
        (true :: (callWord c ++ suffix))).Wd := by
    change 64*(scheduleHint p.1+1)+(callWord c).length+2 ≤
      2^(D*leadOnes (true :: (callWord c ++ suffix)))*K
    rw [StageMain.taggedCall_header_width]
    exact hreq.trans ((Nat.mul_le_mul_left K hypow).trans_eq (Nat.mul_comm _ _))
  constructor <;> omega

end NearQuarticWires.StageCertTests
