import Proof.Quartic.StageCert.BinomialFactor

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the denominator
of the next exact binary binomial-coefficient step is formed literally. -/
def binomialDenominator : St VV MM :=
  .seq (.op (.copy chooseDenominator chooseI)) (.op (.inc chooseDenominator))

/-- `lem:maskpoly`, paper/paper.tex: denominator
construction retains the original recurrence index and every stored field. -/
theorem binomialDenominator_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (i : ℕ) (hi : a.env chooseI=i) (hfit : i+1<2^C.Wd) :
    Hs C binomialDenominator a 3 (fun z=>z.env chooseDenominator=i+1 ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [chooseDenominator]) := by
  unfold binomialDenominator
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C chooseDenominator chooseI a (by decide)) ?_
  rintro b rfl
  refine (hs_inc C chooseDenominator _ (by simp only [DS.set_env_self,hi]; exact hfit)).mono le_rfl ?_
  rintro z rfl
  refine ⟨by simp [hi],rfl,?_,(Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
  exact ⟨by vsimp [chooseDenominator,hc.z],by vsimp [chooseDenominator,hc.one],
    by vsimp [chooseDenominator,hc.two]⟩

/-- `lem:maskpoly`, paper/paper.tex: division uses the
original natural numerator and records its zero remainder before any reduction. -/
def binomialAdvance : St VV MM :=
  .seq (.op (.dm chooseProduct chooseDenominator chooseQuotient chooseRemainder))
    (.seq (.op (.copy chooseValue chooseQuotient)) (.op (.inc chooseI)))

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: one exact binomial update is a fixed number of physical
binary operations, not a unary loop over the coefficient magnitude. -/
theorem binomialAdvance_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n i : ℕ)
    (hi : a.env chooseI=i) (hp : a.env chooseProduct=n.choose i*(n-i))
    (hd : a.env chooseDenominator=i+1) (hfit : 2*(i+1)≤2^C.Wd) :
    Hs C binomialAdvance a 5 (fun z=>z.env chooseValue=n.choose (i+1) ∧
      z.env chooseI=i+1 ∧ z.env chooseRemainder=0 ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [chooseI,chooseValue,chooseQuotient,chooseRemainder]) := by
  have hdiv : n.choose i*(n-i)/(i+1)=n.choose (i+1) := by
    rw [←Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (by omega)
  have hrem : n.choose i*(n-i)%(i+1)=0 := by rw [←Nat.choose_succ_right_eq]; simp
  unfold binomialAdvance
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_dm C chooseProduct chooseDenominator chooseQuotient chooseRemainder a
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hd]; omega) (by rw [hd]; exact hfit)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C chooseValue chooseQuotient _ (by decide)) ?_
  rintro d rfl
  refine (hs_inc C chooseI _ (by
    vsimp [chooseValue,chooseQuotient,chooseRemainder]
    rw [hi]
    omega)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,?_,rfl,?_,?_⟩
  · vsimp [chooseI,chooseValue,chooseQuotient,chooseRemainder,hp,hd]
    exact hdiv
  · vsimp [chooseValue,chooseQuotient,chooseRemainder,hi]
  · vsimp [chooseI,chooseValue,chooseQuotient,chooseRemainder,hp,hd]
    exact hrem
  · exact ⟨by vsimp [chooseI,chooseValue,chooseQuotient,chooseRemainder,hc.z],
      by vsimp [chooseI,chooseValue,chooseQuotient,chooseRemainder,hc.one],
      by vsimp [chooseI,chooseValue,chooseQuotient,chooseRemainder,hc.two]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))))

end NearQuarticWires.StageCert.Tokens
