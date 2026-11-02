import Proof.Quartic.StageLift.ParameterRun
import Proof.Quartic.StageCertTests.PatternClassifier

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:params`, paper/paper.tex:
a fixed number of scalar records is passed by actual sequential reads. -/
def skipParameterRecords : ℕ → St VV MM
  | 0 => skipS
  | n+1 => .seq (.op (.rdM StageLift.parameterStore vJ)) (skipParameterRecords n)

/-- `sec:params` and `prop:time`, paper/paper.tex: skipping retained scalar records charges each read
and leaves the complete source, output and record contents intact. -/
theorem skipParameterRecords_spec (n : ℕ) (C : Ctx) (a : DS VV MM)
    (hroom : a.rc StageLift.parameterStore+n ≤ (a.ram StageLift.parameterStore).length) :
    Hs C (skipParameterRecords n) a (2*n+1) (fun b =>
      b.rc StageLift.parameterStore = a.rc StageLift.parameterStore+n ∧
      b.ram = a.ram ∧ (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧
      Fr a b [vJ]) := by
  induction n generalizing a with
  | zero =>
      refine (skip_spec (C := C) a).mono (by omega) ?_
      rintro b rfl
      exact ⟨by simp,rfl,rfl,Fr.set _ _ (by decide)⟩
  | succ n ih =>
      unfold skipParameterRecords
      refine (Hs.seq (t2 := 2*n+1) (hs_rdM C StageLift.parameterStore vJ a (by omega))
        fun b hb => ?_).mono (by omega) (fun _ h => h)
      subst b
      let start := (a.set vJ ((a.ram StageLift.parameterStore).getD
        (a.rc StageLift.parameterStore) 0)).adv StageLift.parameterStore
      have hstart : start.rc StageLift.parameterStore+n ≤
          (start.ram StageLift.parameterStore).length := by
        simp only [start,DS.adv,DS.set,Function.update_self]
        omega
      refine (ih start hstart).mono le_rfl ?_
      rintro b ⟨hbc,hbr,hbs,hbf⟩
      refine ⟨?_,hbr,hbs,Fr.trans (Fr.set _ _ (by decide)) hbf⟩
      simpa only [start,DS.adv,DS.set,Function.update_self,Nat.add_assoc,Nat.add_comm] using hbc

/-- `sec:params`, paper/paper.tex:
one exact scalar is obtained by rewinding and sequentially reading
the actual retained public parameter block. -/
def selectParameter (index : ℕ) (target : Fin VV) : St VV MM :=
  .seq (.op (.rwM StageLift.parameterStore))
    (.seq (skipParameterRecords index) (.op (.rdM StageLift.parameterStore target)))

/-- `sec:params` and `prop:time`, paper/paper.tex: scalar selection charges its complete head return
and scan; it supplies no decoded parameter oracle. -/
theorem selectParameter_spec (C : Ctx) (a : DS VV MM) (values : List ℕ)
    (index : ℕ) (hi : index < values.length) (target : Fin VV)
    (hv : a.ram StageLift.parameterStore = values) :
    Hs C (selectParameter index target) a (a.rc StageLift.parameterStore+2*index+5)
      (fun b => b.env target = values[index] ∧
        b.rc StageLift.parameterStore = index+1 ∧ b.ram = a.ram ∧
        (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧
        Fr a b [vJ,target]) := by
  unfold selectParameter
  refine (Hs.seq (t2 := 2*index+3) (hs_rwM C StageLift.parameterStore a)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine Hs.seq (t2 := 1) (skipParameterRecords_spec index C (a.rew StageLift.parameterStore)
    (by simp only [DS.rew,Function.update_self,hv];omega)) fun b ⟨hbc,hbr,hbs,hbf⟩ => ?_
  have hc : b.rc StageLift.parameterStore = index := by simpa [DS.rew] using hbc
  have hrd : b.rc StageLift.parameterStore < (b.ram StageLift.parameterStore).length := by
    rw [hc,hbr];change index < (a.ram StageLift.parameterStore).length
    rw [hv];exact hi
  refine (hs_rdM C StageLift.parameterStore target b hrd).mono le_rfl ?_
  rintro d rfl
  refine ⟨?_,by simp [DS.adv,hc],hbr,hbs,?_⟩
  · simp only [DS.adv,DS.set_env_self,hc,hbr]
    change (a.ram StageLift.parameterStore).getD index 0 = _
    rw [hv,List.getD_eq_getElem _ _ hi]
  · exact Fr.trans (Fr.weaken hbf (by simp)) (Fr.set _ _ (by simp))

end NearQuarticWires.StageCertTests
