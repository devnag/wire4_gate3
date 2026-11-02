import Proof.Quartic.StageCertificateControl.PublicBounds
import Proof.Quartic.StageCertificateControl.Censuses
import Proof.Quartic.StageCertTests.CircuitLimit

/-!
# Compute the actual whole-test census from retained public fields

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageCertTests (circuitLimitVar scheduleCallKindVar)

/-- The complete test census of `sec:algorithm`, paper/paper.tex, is computed from the actual call kind and selected chain
length by ordinary bounded arithmetic. -/
def setTestCensus : St VV MM :=
  .seq StageCertTests.setCircuitLimit
    (.seq (setK censusPowerVar 128)
      (.seq (.op (.copy testCountVar (StageCertTests.ScheduleField.variable .chainLength)))
        (.seq (.op (.inc testCountVar))
          (.seq (.op (.mul testCountVar censusPowerVar a1))
            (.seq (.op (.copy testCountVar a1))
              (.seq (.op (.mul testCountVar circuitLimitVar a1))
                (.seq (.op (.copy testCountVar a1)) (.op (.inc testCountVar)))))))))

/-- The exact test-count construction of `sec:algorithm` and
`prop:time`, paper/paper.tex,
uses the real retained kind and chain scalars, leaves every source
and store unchanged, and charges the fixed constant construction. -/
theorem setTestCensus_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (kind : CallKind) (J : ℕ)
    (hk : a.env scheduleCallKindVar=kindTag kind)
    (hJ : a.env (StageCertTests.ScheduleField.variable .chainLength)=J)
    (hfit : 1+StageCertTests.callCircuitCount kind*(128*(J+1))<2^C.Wd) :
    Hs C setTestCensus a 300 (fun b =>
      b.env testCountVar=1+StageCertTests.callCircuitCount kind*(128*(J+1)) ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [circuitLimitVar,censusPowerVar,testCountVar,a1,vJ]) := by
  let cc := StageCertTests.callCircuitCount kind
  have hcc := StageCertTests.callCircuitCount_bounds kind
  have hmid0 := Nat.mul_le_mul_right (128*(J+1)) hcc.1
  simp only [one_mul] at hmid0
  have hmid : 128*(J+1)<2^C.Wd := by omega
  have h128 : 128<2^C.Wd := by nlinarith
  have hJ1 : J+1<2^C.Wd := by nlinarith
  have hprod : (J+1)*128*cc<2^C.Wd := by dsimp [cc];nlinarith
  unfold setTestCensus
  refine (Hs.seq (t2 := 273)
    (StageCertTests.setCircuitLimit_spec C a kind hc hk (by omega))
    fun b ⟨hbc,hbs,hccst,hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbJ : b.env (StageCertTests.ScheduleField.variable .chainLength)=J :=
    (hbf _ (by decide)).trans hJ
  refine Hs.seq (t2 := 13) (setK_spec censusPowerVar (by decide) 128 b h128)
    fun d ⟨hdp,hds,hdf⟩ => ?_
  have hdJ : d.env (StageCertTests.ScheduleField.variable .chainLength)=J :=
    (hdf _ (by decide)).trans hbJ
  have hdc : d.env circuitLimitVar=cc := (hdf _ (by decide)).trans hbc
  refine Hs.seq (t2 := 11)
    (hs_copy C testCountVar (StageCertTests.ScheduleField.variable .chainLength) d (by decide))
    fun e he => ?_
  subst e
  refine Hs.seq (t2 := 9) (hs_inc C testCountVar _ (by simp [hdJ];exact hJ1)) fun e he => ?_
  subst e
  refine Hs.seq (t2 := 7) (hs_mul C testCountVar censusPowerVar a1 _ (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [DS.set,hdJ,hdp];nlinarith)) fun e he => ?_
  subst e
  refine Hs.seq (t2 := 5) (hs_copy C testCountVar a1 _ (by decide)) fun e he => ?_
  subst e
  refine Hs.seq (t2 := 3) (hs_mul C testCountVar circuitLimitVar a1 _ (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [DS.set,hdJ,hdp,hdc];exact hprod)) fun e he => ?_
  subst e
  refine Hs.seq (t2 := 1) (hs_copy C testCountVar a1 _ (by decide)) fun e he => ?_
  subst e
  refine (hs_inc C testCountVar _ (by
    simp (config := {decide := true}) [DS.set,hdJ,hdp,hdc]
    dsimp [cc] at hprod ⊢
    nlinarith)).mono le_rfl ?_
  rintro e he
  have hfr : Fr a e [circuitLimitVar,censusPowerVar,testCountVar,a1,vJ] := by
    subst e
    exact Fr.trans (Fr.weaken hbf (by decide))
      (Fr.trans (Fr.weaken hdf (by decide))
        (Fr.trans (Fr.set (x := testCountVar) _ _ (by decide))
          (Fr.trans (Fr.set (x := testCountVar) _ _ (by decide))
            (Fr.trans (Fr.set (x := a1) _ _ (by decide))
              (Fr.trans (Fr.set (x := testCountVar) _ _ (by decide))
                (Fr.trans (Fr.set (x := a1) _ _ (by decide))
                  (Fr.trans (Fr.set (x := testCountVar) _ _ (by decide)) (Fr.set (x := testCountVar) _ _ (by decide)))))))))
  subst e
  refine ⟨?_,hds.trans hbs,Cst.of_fr hc hfr (by decide),hfr⟩
  simp (config := {decide := true}) [DS.set,hdJ,hdp,hdc]
  dsimp [cc]
  ring

end NearQuarticWires.StageCertificateControl
