import Proof.Quartic.StageFormulaMetadata.TokenLoop

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: both passes
rewind the physically retained raw source and clear their counters. -/
def resetPass : St VV MM :=
  .seq (.op (.rwM 0)) (.seq (.op (.zero consumedVar))
    (.seq (.op (.zero countedTokensVar))
      (.seq (.op (.zero syntaxSizeVar)) (.op (.zero emittedLengthVar)))))

/-- `prop:time`, paper/paper.tex: the actual
rewind pays every retained byte; no loaded source-cursor premise is
introduced, and final output/header bytes remain physically retained. -/
theorem resetPass_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) :
    Hs C resetPass a (a.rc 0+9) (fun b=>
      b.env consumedVar=0 ∧ b.env countedTokensVar=0 ∧ b.env syntaxSizeVar=0 ∧
      b.env emittedLengthVar=0 ∧ b.rc 0=0 ∧ b.ram=a.ram ∧
      (∀ store,store≠0→b.rc store=a.rc store) ∧
      (b.ip,b.out,b.kin,b.kout,b.kc)=(a.ip,a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b [consumedVar,countedTokensVar,syntaxSizeVar,emittedLengthVar]) := by
  unfold resetPass
  refine (Hs.seq (t2:=7) (hs_rwM C 0 a) fun b hb=>?_).mono (by omega) (fun _ h=>h)
  subst b
  refine Hs.seq (t2:=5) (hs_zero C consumedVar _) fun b hb=>?_
  subst b
  refine Hs.seq (t2:=3) (hs_zero C countedTokensVar _) fun b hb=>?_
  subst b
  refine Hs.seq (t2:=1) (hs_zero C syntaxSizeVar _) fun b hb=>?_
  subst b
  refine (hs_zero C emittedLengthVar _).mono le_rfl ?_
  rintro b rfl
  refine ⟨by simp (config:={decide:=true}) [DS.set],
    by simp (config:={decide:=true}) [DS.set],by simp (config:={decide:=true}) [DS.set],
    by simp,by simp [DS.rew],rfl,?_,rfl,?_,?_⟩
  · intro store hstore
    simp only [DS.set_rc,DS.rew,Function.update_of_ne hstore]
  · constructor
    · simpa (config:={decide:=true}) [DS.set,DS.rew] using hc.z
    · simpa (config:={decide:=true}) [DS.set,DS.rew] using hc.one
    · simpa (config:={decide:=true}) [DS.set,DS.rew] using hc.two
  · exact (Fr.set _ _ (by decide)).trans ((Fr.set _ _ (by decide)).trans
      ((Fr.set _ _ (by decide)).trans (Fr.set _ _ (by decide))))

end NearQuarticWires.StageFormulaMetadata
