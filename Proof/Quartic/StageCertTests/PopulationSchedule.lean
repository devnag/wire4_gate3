import Proof.Quartic.StageCertTests.TestRequestEmit
import Proof.Quartic.StageCertTests.ScheduleBounds

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `eq:testX` and `sec:algorithm`, paper/paper.tex: irrelevant population-test ordinals are literal zeros. -/
def zeroTestIndices : St VV MM :=
  .seq (.op (.zero testCircuitVar)) (.seq (.op (.zero signOrdinal)) (.op (.zero testDigitVar)))

/-- `eq:testX`, paper/paper.tex:
the actual population placeholder initializer preserves all source streams. -/
theorem zeroTestIndices_spec (C : Ctx) (a : DS VV MM) :
    Hs C zeroTestIndices a 5 (fun b => b.env testCircuitVar = 0 ∧ b.env signOrdinal = 0 ∧
      b.env testDigitVar = 0 ∧ b.sh = a.sh ∧ Fr a b [testCircuitVar,signOrdinal,testDigitVar]) := by
  unfold zeroTestIndices
  refine Hs.seq (t2 := 3) (hs_zero C testCircuitVar a) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_zero C signOrdinal _) fun b hb => ?_
  subst b
  refine (hs_zero C testDigitVar _).mono le_rfl ?_
  rintro b rfl
  refine ⟨by simp (config := {decide := true}) [DS.set],
    by simp (config := {decide := true}) [DS.set],by simp,rfl,?_⟩
  exact Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))

/-- `sec:algorithm`, paper/paper.tex:
the first required whole-table request is always the population test. -/
def populationSchedule : St VV MM := .seq zeroTestIndices (emitTestRequest .population)

/-- `eq:testX` and `prop:time`, paper/paper.tex: the physical initial whole-test request derives the
literal population threshold from the actual selected parameters. -/
theorem populationSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters) (B : ℕ)
    (hc : Cst a) (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (bounds : ScheduleBounds C p B) :
    Hs C populationSchedule a (14*p.k+200*B+320) (fun b =>
      b.out = a.out ++ (TestMetadata.mk 0 0 0 0 (ThresholdKind.population.threshold p)).word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧ Cst b ∧
      Fr a b ([testCircuitVar,signOrdinal,testDigitVar] ++ testRequestScratch)) := by
  have hsmall : 8 < 2^C.Wd := by have := bounds.small;omega
  unfold populationSchedule
  refine (Hs.seq (t2 := 14*p.k+200*B+300) (zeroTestIndices_spec C a)
    fun b ⟨hbj,hbs,hbr,hbsh,hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbfr (by decide)
  have hbfields : ∀ field : ScheduleField, b.env field.variable = field.value p := by
    intro field
    rw [hbfr _ (by cases field <;> decide),hfields]
  have h0bits : natBitLength 0 ≤ B := by change 1 ≤ B;have := bounds.large;omega
  have hemit := emitTestRequest_spec C b p .population ⟨0,by decide⟩ ⟨0,by decide⟩ 0 B hbc hbfields
    hbj hbs hbr hsmall bounds.exponent (bounds.baseFit .population) (bounds.powerFit .population)
    bounds.large bounds.width bounds.bitFit h0bits (bounds.powerBits .population)
  have hcost : 7*(p.k*ThresholdKind.population.multiplier)+200*B+300 = 14*p.k+200*B+300 := by
    simp only [ThresholdKind.multiplier];ring
  rw [hcost] at hemit
  refine hemit.mono le_rfl ?_
  rintro d ⟨hdo,hdr,hdc,hdfr⟩
  have hbm := Same.of_sh hbsh
  have hrest : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨hbm.ip,hbm.ram,hbm.rc,hbm.kin,hbm.kout,hbm.kc⟩
  refine ⟨?_,hdr.trans hrest,?_,hdc,
    Fr.trans (Fr.weaken hbfr (by intro x hx;exact List.mem_append_left _ hx))
      (Fr.weaken hdfr (by intro x hx;exact List.mem_append_right _ hx))⟩
  · simpa only [ThresholdKind.tag] using hdo.trans (congrArg (· ++
      (TestMetadata.mk 0 0 0 0 (ThresholdKind.population.threshold p)).word) hbm.out)
  · intro field
    rw [hdfr _ (by cases field <;> decide),hbfields]

end NearQuarticWires.StageCertTests
