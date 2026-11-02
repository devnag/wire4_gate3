import Proof.Quartic.StageCert.TupleArithmetic
import Proof.Quartic.StageLift.MemorySource

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `def:mask` and `lem:print`, paper/paper.tex: a source-record scan has its own binary counter. -/
def sourceRecordIndex : Fin VV := ⟨92,by decide⟩
/-- `def:mask` and `lem:print`, paper/paper.tex: the actual selected occurrence or chain-bit address. -/
def sourceRecordLimit : Fin VV := ⟨93,by decide⟩
/-- `def:mask` and `lem:print`, paper/paper.tex: intervening source records are physically read and charged. -/
def sourceRecordDiscard : Fin VV := ⟨94,by decide⟩

/-- `def:mask` and `lem:print`, paper/paper.tex: seek an actual retained source record by rewinding and
reading its finite prefix; no random-access bit oracle is supplied. -/
def seekSourceRecord (store : Fin MM) : St VV MM :=
  .seq (.op (.rwM store))
    (forS sourceRecordIndex sourceRecordLimit (.op (.rdM store sourceRecordDiscard)))

/-- `def:mask` and `lem:print`, paper/paper.tex: a paid source seek retains every actual record and all
external streams while positioning the source cursor at its numeric index. -/
theorem seekSourceRecord_run (C : Ctx) (store : Fin MM) (a : DS VV MM)
    (hc : Cst a) (index : ℕ) (hi : a.env sourceRecordLimit=index)
    (hlen : index≤(a.ram store).length) (hfit : index<2^C.Wd) :
    Hs C (seekSourceRecord store) a (a.rc store+5*index+6) (fun z=>
      z.rc store=index ∧ StageLift.memorySourceRest store z=StageLift.memorySourceRest store a ∧
      Cst z ∧ Fr a z [sourceRecordIndex,sourceRecordDiscard]) := by
  unfold seekSourceRecord
  refine (Hs.seq (t1 := a.rc store+1) (t2 := 5*index+4) (hs_rwM C store a) ?_).mono
    (by omega) (fun _ h=>h)
  rintro b rfl
  let I : ℕ→DS VV MM→Prop := fun k b=>
    b.rc store=k ∧ StageLift.memorySourceRest store b=StageLift.memorySourceRest store a ∧
      Cst b ∧ Fr a b [sourceRecordIndex,sourceRecordDiscard]
  have hset : ∀ k b v,I k b→I k (b.set sourceRecordIndex v) := by
    rintro k b v ⟨br,bs,bc,bf⟩
    exact ⟨br,bs,Cst.of_fr (T := [sourceRecordIndex]) bc (Fr.set _ _ (by simp)) (by decide),
      bf.trans (Fr.set _ _ (by simp))⟩
  have h0 : I 0 (a.rew store) := by
    exact ⟨by simp [DS.rew],by simp [StageLift.memorySourceRest,DS.rew,Function.update_idem],
      ⟨hc.z,hc.one,hc.two⟩,Fr.refl _ _⟩
  refine (forS_spec' (C := C) sourceRecordIndex sourceRecordLimit (by decide)
    (.op (.rdM store sourceRecordDiscard)) (a.rew store) index hfit I 1 hset h0 hi ?_).mono
      (by omega) ?_
  · intro k hk b ⟨br,bs,bc,bf⟩ bindex blimit
    have hram : b.ram=a.ram := congrArg (fun q=>q.2.2.1) bs
    refine (hs_rdM C store sourceRecordDiscard b (by rw [br,hram]; omega)).mono le_rfl ?_
    rintro z rfl
    refine ⟨⟨by simp [DS.adv,DS.set,br],?_,?_,?_⟩,?_,?_⟩
    · exact (show StageLift.memorySourceRest store
        ((b.set sourceRecordDiscard ((b.ram store).getD (b.rc store) 0)).adv store)=
          StageLift.memorySourceRest store b by
        simp [StageLift.memorySourceRest,DS.adv,DS.set,Function.update_idem]).trans bs
    · exact Cst.of_fr (T := [sourceRecordDiscard]) bc (Fr.set _ _ (by simp)) (by decide)
    · exact bf.trans (Fr.set _ _ (by simp))
    · simpa only [DS.adv,DS.set_env_ne _ _ (by decide : sourceRecordIndex≠sourceRecordDiscard)] using bindex
    · simpa only [DS.adv,DS.set_env_ne _ _ (by decide : sourceRecordLimit≠sourceRecordDiscard)] using blimit
  · rintro z ⟨hz,_,_⟩
    exact hz

end NearQuarticWires.StageCert.Tokens
