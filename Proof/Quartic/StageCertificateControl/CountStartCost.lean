import Proof.Quartic.StageCertificateControl.BatchedCost
import Proof.Gates.ENP.TableSeedsCost

/-!
# Polynomial original-source work for the complete count startup

Paper: `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageCertTests (PreparedPolynomial PreparedScheduleRequest)
open NearCubicGates.Close.ENP.TableSearch (PB)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the literal test census is polynomial in
the original call word, uniformly over every witness and default. -/
theorem countHeaderValuePolyCost (B1 B2 : ℕ) :
    Program.PolyCost (fun c _ => countHeaderValue B1 B2 c) := by
  have hupper : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      1+256*(r.selected.1.J+1)) :=
    (PreparedPolynomial.const 1).add
      ((PreparedPolynomial.const 256).mul ((PreparedPolynomial.scalar .chainLength).add
        (PreparedPolynomial.const 1)))
  have hcount : PreparedPolynomial (B1 := B1) (B2 := B2) (fun r =>
      (StageCertTests.certificateMetadata r.selected.1 r.call.kind).length) := by
    refine hupper.mono ?_
    intro r
    have hc := StageCertTests.callCircuitCount_bounds r.call.kind
    rw [StageCertTests.certificateMetadata_length]
    nlinarith
  obtain ⟨K,e,hK⟩ := hcount
  refine ⟨K,e,fun c w => ?_⟩
  cases hd : Program.dispatch B1 B2 c with
  | none => simp [countHeaderValue,hd]
  | some p =>
    have h := hK (PreparedScheduleRequest.mk c w p hd)
    simpa only [countHeaderValue,hd] using h

/-- `prop:time`, paper/paper.tex: the entire
physical count startup, including its source copy, actual compiled
count call, binary header read, head return and full bank erase,
has polynomial cost in the original call word on every input. -/
theorem poolCountPolyCost (B1 B2 : ℕ) : Program.PolyCost (fun c w =>
    poolCountCost (countWord B1 B2 (c,w)).length (countHeaderBudget B1 B2 (c,w))
      (countHeaderValue B1 B2 c)) := by
  let size (r : Call×List Bool) := (callWord r.1).length
  have hw : PB size (fun r => (countWord B1 B2 r).length) := by
    refine ⟨200*(Cells.ParameterArithmetic.preparationCoefficient B1+5),B1+12,fun r => ?_⟩
    exact Cells.all_calls_prepWord_length B1 B2 r.1 r.2
  have hb : PB size (countHeaderBudget B1 B2) := by
    obtain ⟨K,e,hK⟩ := countHeaderPolyCost B1 B2
    exact ⟨K,e,fun r => hK r.1 r.2⟩
  have hc : PB size (fun r => countHeaderValue B1 B2 r.1) := by
    obtain ⟨K,e,hK⟩ := countHeaderValuePolyCost B1 B2
    exact ⟨K,e,fun r => hK r.1 r.2⟩
  have hcp := hc.add (PB.const 1)
  have hsquare : PB size (fun r => (countHeaderValue B1 B2 r.1+1)^2) := by
    simpa only [pow_two] using hcp.mul hcp
  have hupper : PB size (fun r =>
      400*((countWord B1 B2 r).length+countHeaderBudget B1 B2 r+1)+
        2000*(countHeaderValue B1 B2 r.1+1)^2+100) :=
    (((PB.const 400).mul ((hw.add hb).add (PB.const 1))).add
      ((PB.const 2000).mul hsquare)).add (PB.const 100)
  have hactual : PB size (fun r =>
      poolCountCost (countWord B1 B2 r).length (countHeaderBudget B1 B2 r)
        (countHeaderValue B1 B2 r.1)) := by
    apply PB.mono (hg := hupper)
    intro r
    have h := countHeaderReadCost_le (countHeaderValue B1 B2 r.1)
    unfold poolCountCost
    omega
  obtain ⟨K,e,hK⟩ := hactual
  exact ⟨K,e,fun c w => hK (c,w)⟩

end NearQuarticWires.StageCertificateControl
