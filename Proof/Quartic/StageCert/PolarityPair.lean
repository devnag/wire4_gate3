import Proof.Quartic.StageCert.CoefficientToken

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `sec:walks` and `lem:print`, paper/paper.tex: after the mask product, retain the exact positive
summand while serializing all eight signed edge contributions. -/
def cachedPositive : Fin VV := ⟨119,by decide⟩
/-- `sec:walks` and `lem:print`, paper/paper.tex: retain the corresponding exact negative summand. -/
def cachedNegative : Fin VV := ⟨120,by decide⟩

/-- `lem:print`, paper/paper.tex: cache the actual
coefficient pair after its retained-source arithmetic has completed. -/
def cacheCoefficientPair : St VV MM :=
  .seq (.op (.copy cachedPositive linearPositive)) (.op (.copy cachedNegative linearNegative))

/-- `lem:print` and `prop:time`, paper/paper.tex: coefficient caching is two actual binary copies and
does not alter source records, token output or the coefficient itself. -/
theorem cacheCoefficientPair_run (C : Ctx) (positive negative : ℕ)
    (a : DS VV MM) (hc : Cst a) (hp : a.env linearPositive=positive)
    (hn : a.env linearNegative=negative) :
    Hs C cacheCoefficientPair a 3 (fun z=>z.env cachedPositive=positive ∧
      z.env cachedNegative=negative ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [cachedPositive,cachedNegative]) := by
  unfold cacheCoefficientPair
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C cachedPositive linearPositive a (by decide)) ?_
  rintro b rfl
  refine (hs_copy C cachedNegative linearNegative _ (by decide)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by vsimp [hp],by vsimp [hn],rfl,
    Cst.of_fr (T := [cachedPositive,cachedNegative]) hc
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

/-- `sec:walks` and `lem:print`, paper/paper.tex: an original positive sign selects the cached pair;
a negative sign swaps it before exact signed normalization. -/
def selectPolarityPair : St VV MM :=
  .ite (.eq selectedTokenBit v1)
    (.seq (.op (.copy linearPositive cachedPositive)) (.op (.copy linearNegative cachedNegative)))
    (.seq (.op (.copy linearPositive cachedNegative)) (.op (.copy linearNegative cachedPositive)))

/-- `lem:print` and `prop:time`, paper/paper.tex: selecting an edge polarity preserves both cached
summands and implements the complete signed occurrence contribution. -/
theorem selectPolarityPair_run (C : Ctx) (positive negative : ℕ) (sign : Bool)
    (a : DS VV MM) (hc : Cst a) (hp : a.env cachedPositive=positive)
    (hn : a.env cachedNegative=negative) (hs : a.env selectedTokenBit=sign.toNat) :
    Hs C selectPolarityPair a 4 (fun z=>
      z.env linearPositive=(if sign then positive else negative) ∧
      z.env linearNegative=(if sign then negative else positive) ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [linearPositive,linearNegative]) := by
  unfold selectPolarityPair
  refine Hs.ite (t := 3) (c := .eq selectedTokenBit v1)
    (show selectedTokenBit≠v1 by decide) ?_ ?_
  · intro he
    have hsign : sign=true := by
      cases sign with
      | false => simp [Cnd.eval,hs,hc.one] at he
      | true => rfl
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C linearPositive cachedPositive a (by decide)) ?_
    rintro b rfl
    refine (hs_copy C linearNegative cachedNegative _ (by decide)).mono le_rfl ?_
    rintro z rfl
    exact ⟨by vsimp [hp,hsign],by vsimp [hn,hsign],rfl,
      Cst.of_fr (T := [linearPositive,linearNegative]) hc
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
  · intro he
    have hsign : sign=false := by
      cases sign with
      | false => rfl
      | true => simp [Cnd.eval,hs,hc.one] at he
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C linearPositive cachedNegative a (by decide)) ?_
    rintro b rfl
    refine (hs_copy C linearNegative cachedPositive _ (by decide)).mono le_rfl ?_
    rintro z rfl
    exact ⟨by vsimp [hn,hsign],by vsimp [hp,hsign],rfl,
      Cst.of_fr (T := [linearPositive,linearNegative]) hc
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
      (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageCert.Tokens
