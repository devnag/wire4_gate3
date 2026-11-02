import Proof.Quartic.StageCert.SelectedSourceGate
import Proof.Quartic.StageCert.PopulationPrefix

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `def:mask`, paper/paper.tex: the original occurrence
position is distinct from all coordinate and raw-gate work registers. -/
def populationIndex : Fin VV := ⟨136,by decide⟩
/-- `def:mask`, paper/paper.tex: the exact original
occurrence count controls the finite population loop. -/
def populationLimit : Fin VV := ⟨137,by decide⟩

/-- `def:mask`, paper/paper.tex: one original occurrence
updates the selected population and advances both exact occurrence indices. -/
def populationStep : St VV := .seq selectedSourceGate
  (.seq (.op (.inc sourceWitnessIndex)) (.op (.inc populationIndex)))

/-- `def:mask`, paper/paper.tex: the finite population
loop modifies only its counters and the original source evaluator workspace. -/
def populationScratch : List (Fin VV) := populationIndex::sourceWitnessIndex::selectedSourceScratch

/-- `def:mask`, the witness of `sec:algorithm` and `prop:time`,
paper/paper.tex: one complete
source occurrence iteration has an explicit polynomial physical cost. -/
theorem populationStep_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (a : DS VV) (hc : Cst a) (rest pre bits suffix : List Bool) (index : ℕ)
    (hin : C.cw.drop a.cp=gateWord g++rest) (hbase : a.cp≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd)
    (hi : index<bits.length) (hWitnessBase : a.env sourceWitnessBase=pre.length)
    (hindex : a.env sourceWitnessIndex=index)
    (hcw : C.cw=pre++frame bits++suffix) (hfit : a.env populationTotal+2<2^C.Wd)
    (hifit : index+1<2^C.Wd) (hcountfit : a.env populationIndex+1<2^C.Wd) :
    Hs C populationStep a (900*(C.cw.length+2)^2+104) (fun z =>
      z.env populationTotal=a.env populationTotal+
        (if Algorithm.witnessBit bits index then gateMagnitude g (fun l=>a.env (cornerPoint l)) else 0) ∧
      z.env sourceWitnessIndex=index+1 ∧ z.env populationIndex=a.env populationIndex+1 ∧
      z.cp=a.cp+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z populationScratch) := by
  unfold populationStep
  apply Hx.hs
  refine Hs.then (selectedSourceGate_run C g a hc rest pre bits suffix index hin hbase hW hpoint
    hi hWitnessBase hindex hcw hfit)
    (fun b ⟨bt,bc,bw,bo,bconst,bfr⟩ n1 hn1 => ?_)
  have bi : b.env sourceWitnessIndex=index := (bfr _ (by decide) (by decide)).trans hindex
  have bj : b.env populationIndex=a.env populationIndex := bfr _ (by decide) (by decide)
  refine Hs.then (hs_inc C sourceWitnessIndex b (by rw [bi]; exact hifit))
    (fun d hd n2 hn2 => ?_)
  subst hd
  refine Hs.last (hs_inc C populationIndex _
    (by rw [DS.set_env_ne _ _ (by decide),bj]; exact hcountfit))
    (fun z hz n3 hn3 => ?_)
  subst hz
  refine ⟨⟨?_,?_,?_,bc,bw,bo,?_,?_⟩,?_⟩
  · simpa only [DS.set_env_ne _ _ (by decide : populationTotal≠populationIndex),
      DS.set_env_ne _ _ (by decide : populationTotal≠sourceWitnessIndex),gateMagnitude] using bt
  · simp only [DS.set_env_ne _ _ (by decide : sourceWitnessIndex≠populationIndex),DS.set_env_self,bi]
  · simp only [DS.set_env_self,DS.set_env_ne _ _ (by decide : populationIndex≠sourceWitnessIndex),bj]
  · exact ⟨by vsimp [sourceWitnessIndex,populationIndex,bconst.z],
      by vsimp [sourceWitnessIndex,populationIndex,bconst.one],
      by vsimp [sourceWitnessIndex,populationIndex,bconst.two],
      by vsimp [sourceWitnessIndex,populationIndex,bconst.pos]⟩
  · exact (bfr.weaken (by decide)).trans
      (((Fr.set (T := [sourceWitnessIndex]) _ _ (by simp)).toS.weaken (by decide)).trans
        ((Fr.set (T := [populationIndex]) _ _ (by simp)).toS.weaken (by decide)))
  · omega

end NearQuarticWires.StageCert
