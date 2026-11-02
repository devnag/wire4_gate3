import Proof.Quartic.StageCertTests.PatternSchedule

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:cycle` and `sec:algorithm`, paper/paper.tex: only nonzero signed trace weights
require the complete digit and final-error moment tests. -/
noncomputable def activePatternMetadata (p : Cells.Parameters) (j : Fin 2) (code : Fin 256) :
    List TestMetadata :=
  if Cycle.kappa 4 (patternOfCode code.val) ≠ 0 then patternMetadataList p j code else []

/-- `sec:algorithm`, paper/paper.tex:
the actual binary κ classifier controls the whole-test scheduler. -/
def activePatternSchedule : St VV MM :=
  .seq classifySignPattern (.ite (.eq signActive v1) patternSchedule skipS)

/-- `sec:algorithm`, paper/paper.tex:
classification and test generation use an explicit bounded scratch set. -/
def activePatternScratch : List (Fin VV) :=
  [signCode,signSum,signBit,signQuotient,signActive] ++ digitScheduleScratch

/-- `sec:cycle` and `prop:time`, paper/paper.tex: the actual κ branch emits precisely the required
whole-pattern requests, including the empty output for zero weight. -/
theorem activePatternSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (j : Fin 2) (code : Fin 256) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hj : a.env testCircuitVar = j.val) (hs : a.env signOrdinal = code.val)
    (bounds : ScheduleBounds C p B) :
    Hs C activePatternSchedule a ((p.J+1)*(56*p.k+200*B+310)+90) (fun b =>
      b.out = a.out ++ (activePatternMetadata p j code).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
      b.env testCircuitVar = j.val ∧ b.env signOrdinal = code.val ∧ Cst b ∧
      Fr a b activePatternScratch) := by
  have hsmall : 8 < 2^C.Wd := by have := bounds.small;omega
  unfold activePatternSchedule
  refine (Hs.seq (t2 := (p.J+1)*(56*p.k+200*B+310)+25)
    (classifySignPattern_spec C a hc code hs (by omega) hsmall)
    fun b ⟨hbactive,hbs,hbsh,hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbfr (by decide)
  have hbfields : ∀ field : ScheduleField, b.env field.variable = field.value p := by
    intro field
    rw [hbfr _ (by cases field <;> decide),hfields]
  have hbj : b.env testCircuitVar = j.val := by rw [hbfr _ (by decide),hj]
  have hbm := Same.of_sh hbsh
  have hrest : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨hbm.ip,hbm.ram,hbm.rc,hbm.kin,hbm.kout,hbm.kc⟩
  classical
  by_cases hk : Cycle.kappa 4 (patternOfCode code.val) ≠ 0
  · have heval : (Cnd.eq signActive v1).eval b = true := by simp [Cnd.eval,hbactive,hbc.one,hk]
    refine (Hs.iteT (c := .eq signActive v1) (show signActive ≠ v1 by decide) heval
      (patternSchedule_spec C b p j code B hbc hbfields hbj hbs bounds)).mono (by omega) ?_
    rintro d ⟨hdo,hdr,hdf,hdj,hds,hdc,hdfr⟩
    refine ⟨?_,hdr.trans hrest,hdf,hdj,hds,hdc,
      Fr.trans (Fr.weaken hbfr (by decide)) (Fr.weaken hdfr (by intro x hx;exact List.mem_append_right _ hx))⟩
    rw [hdo,hbm.out]
    simp [activePatternMetadata,hk]
  · have heval : (Cnd.eq signActive v1).eval b = false := by simp [Cnd.eval,hbactive,hbc.one,hk]
    refine (Hs.iteF (c := .eq signActive v1) (show signActive ≠ v1 by decide) heval (skip_spec (C := C) b)).mono (by omega) ?_
    rintro d rfl
    refine ⟨?_,hrest,?_,hbj,hbs,Cst.of_fr (T := [vJ]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans (Fr.weaken hbfr (by decide)) (Fr.set _ _ (by decide))⟩
    · change b.out = _
      rw [hbm.out]
      simp [activePatternMetadata,hk]
    · intro field
      simpa (config := {decide := true}) [DS.set,show field.variable ≠ vJ by cases field <;> decide] using hbfields field

end NearQuarticWires.StageCertTests
