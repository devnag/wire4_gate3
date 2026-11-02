import Proof.Quartic.StageCert.SourceMetadata

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testE` and `eq:testPhi`, paper/paper.tex:
digits retain their requested row; final error uses the original last row. -/
def selectMomentRow : St VV MM :=
  .ite (.eq sourceTestTag v1) skipS
    (.seq (.op (.copy requestedChainRow chainRows)) (.op (.sub requestedChainRow v1)))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual test tag determines the retained digit or
last-chain row by physical bounded branching, with source bytes unchanged. -/
theorem selectMomentRow_run (C : Ctx) (tag row J : ℕ) (a : DS VV MM) (hc : Cst a)
    (ht : a.env sourceTestTag=tag) (hr : a.env requestedChainRow=row)
    (hJ : a.env chainRows=J) (hpos : 1≤J) :
    Hs C selectMomentRow a 4 (fun z=>
      z.env requestedChainRow=(if tag=1 then row else J-1) ∧ z.sh=a.sh ∧
      Cst z ∧ Fr a z [requestedChainRow,vJ]) := by
  unfold selectMomentRow
  refine Hs.ite (t := 3) (c := .eq sourceTestTag v1)
    (show sourceTestTag≠v1 by decide) ?_ ?_
  · intro he
    have htag : tag=1 := by simpa only [Cnd.eval,ht,hc.one,decide_eq_true_eq] using he
    refine (skip_spec a).mono (by omega) ?_
    rintro z rfl
    exact ⟨by rw [if_pos htag,DS.set_env_ne _ _ (by decide)]; exact hr,rfl,
      Cst.of_fr (T := [vJ]) hc (Fr.set _ _ (by simp)) (by decide),Fr.set _ _ (by simp)⟩
  · intro he
    have htag : tag≠1 := by simpa only [Cnd.eval,ht,hc.one,decide_eq_false_iff_not] using he
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C requestedChainRow chainRows a (by decide)) ?_
    rintro b rfl
    refine (hs_sub C requestedChainRow v1 _ (by decide)
      (by vsimp [hJ,hc.one]; exact hpos)).mono le_rfl ?_
    rintro z rfl
    exact ⟨by rw [if_neg htag]; vsimp [hJ,hc.one],rfl,
      Cst.of_fr (T := [requestedChainRow]) hc
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageCert.Tokens
