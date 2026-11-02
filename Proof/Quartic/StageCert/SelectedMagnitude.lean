import Proof.Quartic.StageCert.DeltaGate
import Proof.Quartic.StageCert.SourceWitness

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Dispatch

/-- `def:mask`, paper/paper.tex: the original selected
population is accumulated without identifying repeated gate occurrences. -/
def populationTotal : Fin VV := ⟨135,by decide⟩

/-- `def:mask`, paper/paper.tex: only a literal selected
witness bit adds the occurrence's exact absolute mixed difference. -/
def addSelectedMagnitude : St VV := .ite (.eq sourceWitnessResult v1)
  (.op (.add populationTotal deltaMagnitude)) skipS

/-- `def:mask`, paper/paper.tex: the selected-population
update is exact for either Boolean witness value. -/
theorem addSelectedMagnitude_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (selected : Bool) (hs : a.env sourceWitnessResult=selected.toNat)
    (hfit : a.env populationTotal+a.env deltaMagnitude<2^C.Wd) :
    Hs C addSelectedMagnitude a 2 (fun z =>
      z.env populationTotal=a.env populationTotal+(if selected then a.env deltaMagnitude else 0) ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z [populationTotal,vJ]) := by
  unfold addSelectedMagnitude
  refine Hs.ite (c := .eq sourceWitnessResult v1) (show sourceWitnessResult≠v1 by decide) ?_ ?_
  · intro he
    have hselected : selected=true := by cases selected <;> simp_all [Cnd.eval,Bool.toNat,hc.one]
    refine (hs_add C populationTotal deltaMagnitude a (by decide) hfit).mono le_rfl ?_
    rintro z rfl
    refine ⟨by simp [hselected],rfl,rfl,rfl,?_,Fr.set _ _ (by simp)⟩
    exact Cst.of_fr hc (Fr.set (T := [populationTotal]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  · intro he
    have hselected : selected=false := by cases selected <;> simp_all [Cnd.eval,Bool.toNat,hc.one]
    refine (skip_spec a).mono le_rfl ?_
    rintro z rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide)]; simp [hselected],rfl,rfl,rfl,?_,Fr.set _ _ (by simp)⟩
    exact Cst.of_fr hc (Fr.set (T := [vJ]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)

end NearQuarticWires.StageCert
