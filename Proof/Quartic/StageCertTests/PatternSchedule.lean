import Proof.Quartic.StageCertTests.DigitSchedule
import Proof.Quartic.StageCertTests.ScheduleBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `eq:testE`–`eq:testPhi`, paper/paper.tex:
all selected digit requests precede the final-error request for
each required circuit and sign pattern. -/
def patternMetadataList (p : Cells.Parameters) (j : Fin 2) (code : Fin 256) : List TestMetadata :=
  digitMetadataList p j code ++ [⟨2,j.val,code.val,0,ThresholdKind.finalError.threshold p⟩]

/-- `sec:algorithm`, paper/paper.tex:
one physical pattern scheduler emits all chain tests and then
the final-error request with its literal zero digit placeholder. -/
def patternSchedule : St VV MM :=
  .seq digitSchedule (.seq (setK testDigitVar 0) (emitTestRequest .finalError))

/-- `eq:testE`–`eq:testPhi` and `prop:time`, paper/paper.tex: the complete required pattern schedule
is physically printed at polynomial cost in the selected parameters. -/
theorem patternSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (j : Fin 2) (code : Fin 256) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hj : a.env testCircuitVar = j.val) (hs : a.env signOrdinal = code.val)
    (bounds : ScheduleBounds C p B) :
    Hs C patternSchedule a ((p.J+1)*(56*p.k+200*B+310)+20) (fun b =>
      b.out = a.out ++ (patternMetadataList p j code).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
      b.env testCircuitVar = j.val ∧ b.env signOrdinal = code.val ∧ Cst b ∧
      Fr a b digitScheduleScratch) := by
  have hsmall : 8 < 2^C.Wd := by have := bounds.small;omega
  unfold patternSchedule
  refine (Hs.seq (t2 := 56*p.k+200*B+304)
    (digitSchedule_spec C a p j code B hc hfields hj hs hsmall bounds.exponent
      (bounds.baseFit .digit) (bounds.powerFit .digit) bounds.large bounds.width bounds.bitFit
      bounds.chainBits bounds.chainFit (bounds.powerBits .digit))
    fun b ⟨hbo,hbr,hbf,hbj,hbs,hbc,hbfr⟩ => ?_).mono (by nlinarith) (fun _ h => h)
  refine (Hs.seq (t2 := 56*p.k+200*B+300) (setK_spec testDigitVar (by decide) 0 b (by omega))
    fun d ⟨hdv,hdsh,hdfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hdc : Cst d := Cst.of_fr hbc hdfr (by decide)
  have hdfields : ∀ field : ScheduleField, d.env field.variable = field.value p := by
    intro field
    rw [hdfr _ (by cases field <;> decide),hbf]
  have hdj : d.env testCircuitVar = j.val := by rw [hdfr _ (by decide),hbj]
  have hds : d.env signOrdinal = code.val := by rw [hdfr _ (by decide),hbs]
  have hp0 : natBitLength 0 ≤ B := by change 1 ≤ B;have := bounds.large;omega
  have hemit := emitTestRequest_spec C d p .finalError j code 0 B hdc hdfields hdj hds hdv
    hsmall bounds.exponent (bounds.baseFit .finalError) (bounds.powerFit .finalError)
    bounds.large bounds.width bounds.bitFit hp0 (bounds.powerBits .finalError)
  have hcost : 7*(p.k*ThresholdKind.finalError.multiplier)+200*B+300 = 56*p.k+200*B+300 := by
    simp only [ThresholdKind.multiplier];ring
  rw [hcost] at hemit
  refine hemit.mono le_rfl ?_
  rintro e ⟨heo,her,hec,hefr⟩
  have hdm := Same.of_sh hdsh
  have hdrest : (d.ip,d.ram,d.rc,d.kin,d.kout,d.kc) = (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨hdm.ip,hdm.ram,hdm.rc,hdm.kin,hdm.kout,hdm.kc⟩
  refine ⟨?_,her.trans (hdrest.trans hbr),?_,?_,?_,hec,?_⟩
  · rw [heo,hdm.out,hbo]
    simp [patternMetadataList,ThresholdKind.tag,List.append_assoc]
  · intro field
    rw [hefr _ (by cases field <;> decide),hdfields]
  · rw [hefr _ (by decide),hdj]
  · rw [hefr _ (by decide),hds]
  · exact Fr.trans hbfr (Fr.trans (Fr.weaken hdfr (by decide))
      (Fr.weaken hefr (by intro x hx;exact List.mem_cons_of_mem _ hx)))

end NearQuarticWires.StageCertTests
