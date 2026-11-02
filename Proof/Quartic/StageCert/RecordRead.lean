import Proof.Quartic.StageCert.RecordAt
import Proof.Quartic.StageCert.SelectedSquareToken

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `def:mask` and `lem:print`, paper/paper.tex: the source record at its actual numeric index is reached
by a paid rewind and prefix scan, then read into a retained field. -/
def readSourceRecord (store : Fin MM) (target : Fin VV) : St VV MM :=
  .seq (seekSourceRecord store) (.op (.rdM store target))

/-- `def:mask` and `lem:print`, paper/paper.tex: the returned value is the original retained source record,
not a supplied decoded occurrence bit, parameter, or chain coefficient. -/
theorem readSourceRecord_run (C : Ctx) (store : Fin MM) (target : Fin VV)
    (htarget : target≠vZ ∧ target≠v1 ∧ target≠v2)
    (a : DS VV MM) (hc : Cst a) (index : ℕ) (hi : a.env sourceRecordLimit=index)
    (hlen : index<(a.ram store).length) (hfit : index<2^C.Wd) :
    Hs C (readSourceRecord store target) a (a.rc store+5*index+8) (fun z=>
      z.env target=(a.ram store).getD index 0 ∧ z.rc store=index+1 ∧
      StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      Cst z ∧ Fr a z [target,sourceRecordIndex,sourceRecordDiscard]) := by
  unfold readSourceRecord
  refine (Hs.seq (t1 := a.rc store+5*index+6) (t2 := 1)
    (seekSourceRecord_run C store a hc index hi hlen.le hfit) ?_).mono le_rfl (fun _ h=>h)
  rintro b ⟨br,bs,bc,bfr⟩
  have hram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
  refine (hs_rdM C store target b (by rw [br,hram]; exact hlen)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,by simp [DS.adv,DS.set,br],?_,?_,?_⟩
  · simp only [DS.adv,DS.set_env_self,hram,br]
  · exact (show StageLift.memorySourceRest store
      ((b.set target ((b.ram store).getD (b.rc store) 0)).adv store)=
        StageLift.memorySourceRest store b by
      simp [StageLift.memorySourceRest,DS.adv,DS.set,Function.update_idem]).trans bs
  · exact Cst.of_fr (T := [target]) bc (Fr.set _ _ (by simp))
      (by simpa only [List.mem_singleton] using ⟨Ne.symm htarget.1,Ne.symm htarget.2.1,Ne.symm htarget.2.2⟩)
  · exact (bfr.weaken (by intro x hx; exact List.mem_cons_of_mem _ hx)).trans (Fr.set _ _ (by simp))

end NearQuarticWires.StageCert.Tokens
