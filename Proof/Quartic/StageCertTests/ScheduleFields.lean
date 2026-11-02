import Proof.Quartic.StageCertTests.ParameterSelect

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `eq:testX`–`eq:testPhi` and `sec:params`, paper/paper.tex: five retained parameters control the
whole-test schedule and its strict scalar thresholds. -/
inductive ScheduleField where
  | k | populationBase | digitBase | chainLength | errorBase
  deriving DecidableEq

/-- `sec:params`, paper/paper.tex:
each scheduler scalar has its exact position in the public parameter codec. -/
def ScheduleField.index : ScheduleField → ℕ
  | .k => 6 | .populationBase => 12 | .digitBase => 27
  | .chainLength => 40 | .errorBase => 42

/-- `sec:params`, paper/paper.tex:
the scheduling fields occupy distinct retained registers. -/
def ScheduleField.variable : ScheduleField → Fin VV
  | .k => ⟨74,by decide⟩ | .populationBase => ⟨75,by decide⟩
  | .digitBase => ⟨76,by decide⟩ | .chainLength => ⟨77,by decide⟩
  | .errorBase => ⟨78,by decide⟩

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
these are the literal selected values used by the certificate tests. -/
def ScheduleField.value (p : Cells.Parameters) : ScheduleField → ℕ
  | .k => p.k | .populationBase => p.Xmax | .digitBase => p.hE
  | .chainLength => p.J | .errorBase => p.Lambda

/-- `sec:params`, paper/paper.tex:
every scheduler field belongs to the fixed retained scalar block. -/
theorem ScheduleField.index_lt (field : ScheduleField) : field.index < 46 := by
  cases field <;> decide

/-- `sec:params`, paper/paper.tex:
the selected record is the exact public scalar, including the
tail positions after rational and prime-list components. -/
theorem ScheduleField.getD (field : ScheduleField) (p : Cells.Parameters) :
    (StageLift.parameterScalars p).getD field.index 0 = field.value p := by
  cases field <;> rfl

/-- `sec:params`, paper/paper.tex:
retained scheduling variables are pairwise distinct. -/
theorem ScheduleField.variable_injective : Function.Injective ScheduleField.variable := by
  intro x y h
  cases x <;> cases y <;> simp_all [ScheduleField.variable]

/-- `sec:params` and `prop:time`, paper/paper.tex: a scheduling scalar is physically fetched from the
actual shared parameter store, with its head return fully charged. -/
theorem selectScheduleField_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (field : ScheduleField) (hparams : a.ram StageLift.parameterStore = StageLift.parameterScalars p)
    (hcursor : a.rc StageLift.parameterStore ≤ 46) :
    Hs C (selectParameter field.index field.variable) a 150 (fun b =>
      b.env field.variable = field.value p ∧ b.rc StageLift.parameterStore ≤ 46 ∧
      b.ram = a.ram ∧ (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧
      Fr a b [vJ,field.variable]) := by
  have hi : field.index < (StageLift.parameterScalars p).length := by
    rw [StageLift.parameterScalars_length];exact field.index_lt
  refine (selectParameter_spec C a (StageLift.parameterScalars p) field.index hi
    field.variable hparams).mono (by have := field.index_lt;omega) ?_
  rintro b ⟨hb,hbc,hbr,hbs,hbf⟩
  refine ⟨?_,by have := field.index_lt;omega,hbr,hbs,hbf⟩
  rw [←List.getD_eq_getElem _ _ hi,field.getD] at hb
  exact hb

end NearQuarticWires.StageCertTests
