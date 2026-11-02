import Proof.Quartic.StageCertTests.CircuitSchedule
import Proof.Quartic.StageCertTests.PopulationSchedule

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:algorithm`, paper/paper.tex:
the complete physical metadata sequence starts with population,
then contains every required circuit, sign, digit and final-error test. -/
noncomputable def certificateMetadata (p : Cells.Parameters) (kind : CallKind) : List TestMetadata :=
  ⟨0,0,0,0,ThresholdKind.population.threshold p⟩ ::
    circuitMetadataForLimit p (callCircuitCount kind) (callCircuitCount_bounds kind).2

/-- `sec:algorithm`, paper/paper.tex:
one fixed program prints the complete whole-test request schedule. -/
def wholeSchedule : St VV MM := .seq populationSchedule allCircuitSchedule

/-- `prop:time`, paper/paper.tex:
the complete scheduler source clock charges every nested loop,
classification, scalar power and emitted metadata bit. -/
def wholeScheduleSteps (p : Cells.Parameters) (B : ℕ) : ℕ :=
  (14*p.k+200*B+320)+(2*(256*((p.J+1)*(56*p.k+200*B+310)+100)+604)+20)+1

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: all actual whole-test requests are
physically generated, with no supplied plan or scalar-threshold oracle. -/
theorem wholeSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (kind : CallKind) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hk : a.env scheduleCallKindVar = kindTag kind) (bounds : ScheduleBounds C p B) :
    Hs C wholeSchedule a (wholeScheduleSteps p B) (fun b =>
      b.out = a.out ++ (certificateMetadata p kind).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧ Cst b) := by
  unfold wholeSchedule wholeScheduleSteps
  refine Hs.seq (populationSchedule_spec C a p B hc hfields bounds)
    fun b ⟨hbo,hbr,hbf,hbc,hbfr⟩ => ?_
  have hbk : b.env scheduleCallKindVar = kindTag kind := by rw [hbfr _ (by decide),hk]
  refine (allCircuitSchedule_spec C b p kind B hbc hbf hbk bounds).mono le_rfl ?_
  rintro d ⟨hdo,hdr,_,hdc,_⟩
  refine ⟨?_,hdr.trans hbr,hdc⟩
  rw [hdo,hbo]
  simp [certificateMetadata,List.append_assoc]

end NearQuarticWires.StageCertTests
