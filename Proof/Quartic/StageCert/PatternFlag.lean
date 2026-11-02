import Proof.Quartic.StageCert.PatternArithmetic
import Proof.Quartic.StageCert.IncidenceHeavy

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: one visited coordinate
retains a side flag precisely when its actual raw incidence is below `dstar`. -/
def keepNonheavy : St VV :=
  .ite (.lt censusTotal heavyThreshold) skipS (.op (.zero patternFlag))

/-- `def:mask`, paper/paper.tex: the inclusive heavy test
updates the accumulated side flag by exact Boolean conjunction. -/
theorem keepNonheavy_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (P : Prop) [Decidable P] (hflag : a.env patternFlag=bnat P) :
    Hs C keepNonheavy a 2 (fun b =>
      b.env patternFlag=bnat (P ∧ a.env censusTotal<a.env heavyThreshold) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b [vJ,patternFlag]) := by
  unfold keepNonheavy
  refine Hs.ite (c := .lt censusTotal heavyThreshold)
    (show censusTotal≠heavyThreshold by decide) ?_ ?_
  · intro he
    have hl : a.env censusTotal<a.env heavyThreshold := by
      simpa only [Cnd.eval,decide_eq_true_eq] using he
    refine (skip_spec a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide),hflag]; simp only [hl,and_true],rfl,rfl,rfl,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩,Fr.set _ _ (by simp)⟩
  · intro he
    have hl : ¬a.env censusTotal<a.env heavyThreshold := by
      simpa only [Cnd.eval,decide_eq_false_iff_not] using he
    refine (hs_zero C patternFlag a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [bnat,hl],rfl,rfl,rfl,
      ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
       by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩,Fr.set _ _ (by simp)⟩

end NearQuarticWires.StageCert.Incidence
