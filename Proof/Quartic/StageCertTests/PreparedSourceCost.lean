import Proof.Quartic.StageCertTests.PreparedPolynomial
import Proof.Quartic.StageCertTests.ParameterReadCost

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

variable {B1 B2 : ℕ}

/-- `prop:time`, paper/paper.tex:
the literal arity header pays its own binary field length. -/
theorem PreparedPolynomial.arityBits : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => natBitLength r.call.n) := by
  refine PreparedPolynomial.callLength.mono ?_
  intro r
  have hn : (natWord r.call.n).length ≤ (callWord r.call).length := by simp [callWord]
  rw [natWord_length] at hn
  omega

/-- `prop:time`, paper/paper.tex:
the three original call-kind tags have constant binary height. -/
theorem PreparedPolynomial.kindBits : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => natBitLength (kindTag r.call.kind)) := by
  refine (PreparedPolynomial.const 2).mono ?_
  intro r
  cases r.call.kind <;> decide

/-- `prop:time`, paper/paper.tex:
the complete actual parameter decoder is polynomial in the
original call, including both counted list payloads. -/
theorem PreparedPolynomial.parameterReader : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => StageLift.parameterReadCost r.selected.1 (scheduleHint r.selected.1)) := by
  have h : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      5000*((Program.parametersWord r.selected.1).length+1)*(scheduleHint r.selected.1+1)) :=
    ((PreparedPolynomial.const 5000).mul
    (PreparedPolynomial.parameterLength.add (PreparedPolynomial.const 1))).mul
      (PreparedPolynomial.hint.add (PreparedPolynomial.const 1))
  exact h.mono fun r => parameterReadCost_le_word r.selected.1 (scheduleHint r.selected.1)

/-- `prop:time`, paper/paper.tex:
a polynomial majorant combines only actual original-source sizes
and the complete paid parameter decoder clock. -/
def prepScheduleMass (c : Call) (p : Cells.Parameters) : ℕ :=
  ((callWord c).length+1)+(scheduleHint p+1)+(p.k+1)+(p.J+1)+
    StageLift.parameterReadCost p (scheduleHint p)+natBitLength c.n+natBitLength (kindTag c.kind)+1

/-- `prop:time`, paper/paper.tex:
the complete explicit source clock is below a fixed fourth power
of its actual polynomial source and parameter quantities. -/
theorem prepScheduleSteps_le_mass (c : Call) (p : Cells.Parameters) :
    prepScheduleSteps c p ≤ 10^8*(prepScheduleMass c p)^4 := by
  let A := prepScheduleMass c p
  have hA : 1 ≤ A := by dsimp [A,prepScheduleMass];omega
  have hL : (callWord c).length+1 ≤ A := by dsimp [A,prepScheduleMass];omega
  have hB : scheduleHint p ≤ A := by dsimp [A,prepScheduleMass];omega
  have hk : p.k ≤ A := by dsimp [A,prepScheduleMass];omega
  have hJ : p.J+1 ≤ A := by dsimp [A,prepScheduleMass];omega
  have hP : StageLift.parameterReadCost p (scheduleHint p) ≤ A := by dsimp [A,prepScheduleMass];omega
  have hn : natBitLength c.n ≤ A := by dsimp [A,prepScheduleMass];omega
  have ht : natBitLength (kindTag c.kind) ≤ A := by dsimp [A,prepScheduleMass];omega
  have hcube := Nat.pow_le_pow_left hL 3
  have hq : 56*p.k+200*scheduleHint p+310 ≤ 566*A := by omega
  have hloop := Nat.mul_le_mul hJ hq
  have hA2 : A ≤ A^2 := by nlinarith
  have hA3 : A^2 ≤ A^3 := by nlinarith
  have hA4 : A^3 ≤ A^4 := by nlinarith
  change prepScheduleSteps c p ≤ 10^8*A^4
  unfold prepScheduleSteps wholeScheduleSteps
  nlinarith only [hA,hL,hB,hk,hP,hn,ht,hcube,hloop,hA2,hA3,hA4]

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the complete original-source scheduler
clock is polynomial in the actual original call word, uniformly
over all witness suffixes and both active-circuit branches. -/
theorem PreparedPolynomial.sourceSteps : PreparedPolynomial (B1 := B1) (B2 := B2)
    (fun r => prepScheduleSteps r.call r.selected.1) := by
  have hL : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => (callWord r.call).length) :=
    PreparedPolynomial.callLength
  have hB : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => scheduleHint r.selected.1) :=
    PreparedPolynomial.hint
  have hk : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => r.selected.1.k) :=
    PreparedPolynomial.scalar .k
  have hJ : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r => r.selected.1.J) :=
    PreparedPolynomial.scalar .chainLength
  have hp := PreparedPolynomial.parameterReader (B1 := B1) (B2 := B2)
  have hn := PreparedPolynomial.arityBits (B1 := B1) (B2 := B2)
  have ht := PreparedPolynomial.kindBits (B1 := B1) (B2 := B2)
  have hmass : PreparedPolynomial (B1 := B1) (B2 := B2)
      (fun r => prepScheduleMass r.call r.selected.1) :=
    (((((((hL.add (PreparedPolynomial.const 1)).add (hB.add (PreparedPolynomial.const 1))).add
      (hk.add (PreparedPolynomial.const 1))).add (hJ.add (PreparedPolynomial.const 1))).add hp).add hn).add ht).add
        (PreparedPolynomial.const 1)
  have hfinal : PreparedPolynomial (B1 := B1) (B2 := B2)
      (fun r => 10^8*(prepScheduleMass r.call r.selected.1)^4) :=
    (PreparedPolynomial.const (10^8)).mul (hmass.pow 4)
  exact hfinal.mono fun r => prepScheduleSteps_le_mass r.call r.selected.1

end NearQuarticWires.StageCertTests
