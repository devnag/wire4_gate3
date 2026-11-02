import Proof.Quartic.StageCert.OriginalEdgeTokens
import Proof.Quartic.StageLift.NewtonCoefficient

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the upper
argument of the exact binary binomial-coefficient computation. -/
def chooseN : Fin VV := ⟨110,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the lower
argument of the exact binary binomial-coefficient computation. -/
def chooseR : Fin VV := ⟨111,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the current
coefficient index of the finite binomial recurrence. -/
def chooseI : Fin VV := ⟨112,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the exact current
binomial coefficient, stored in binary. -/
def chooseValue : Fin VV := ⟨113,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the natural
multiplicative factor `n-i` in the next binomial recurrence. -/
def chooseFactor : Fin VV := ⟨114,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the positive
natural denominator `i+1` is retained before exact integer division. -/
def chooseDenominator : Fin VV := ⟨115,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the exact binary
numerator is computed before any modular reduction. -/
def chooseProduct : Fin VV := ⟨116,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: exact divisibility
is retained as a zero remainder, rather than division modulo a composite. -/
def chooseRemainder : Fin VV := ⟨117,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the next exact
binary coefficient is the quotient of the original natural numerator. -/
def chooseQuotient : Fin VV := ⟨118,by decide⟩

/-- `lem:maskpoly`, paper/paper.tex: form the exact
natural numerator `choose(n,i)*(n-i)` by binary arithmetic. -/
def binomialFactor : St VV MM := .seq (.op (.copy chooseFactor chooseN))
  (.seq (.op (.sub chooseFactor chooseI)) (.op (.mul chooseValue chooseFactor chooseProduct)))

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: the multiplicative binomial recurrence retains exact
integer values and a polynomial binary-height bound. -/
theorem binomialFactor_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n i : ℕ)
    (hn : a.env chooseN=n) (hi : a.env chooseI=i) (hv : a.env chooseValue=n.choose i)
    (hin : i≤n) (hfit : 2^n*(n+1)<2^C.Wd) :
    Hs C binomialFactor a 5 (fun z=>
      z.env chooseFactor=n-i ∧ z.env chooseProduct=n.choose i*(n-i) ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [chooseFactor,chooseProduct]) := by
  have hprod : n.choose i*(n-i)<2^C.Wd :=
    lt_of_le_of_lt (Nat.mul_le_mul (Nat.choose_le_two_pow n i) (show n-i≤n+1 by omega)) hfit
  unfold binomialFactor
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C chooseFactor chooseN a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C chooseFactor chooseI _ (by decide)
    (by simp only [DS.set_env_self,DS.set_env_ne _ _ (by decide : chooseI≠chooseFactor)]; rw [hn,hi]; exact hin)) ?_
  rintro d rfl
  refine (hs_mul C chooseValue chooseFactor chooseProduct _ (by decide) (by decide) (by decide)
    (by simp only [DS.set_env_self,DS.set_env_ne _ _ (by decide : chooseValue≠chooseFactor),
      DS.set_env_ne _ _ (by decide : chooseI≠chooseFactor)]; rw [hn,hi,hv]; exact hprod)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,?_,?_⟩
  · vsimp [chooseFactor,chooseProduct,hn,hi]
  · vsimp [chooseFactor,chooseProduct,hn,hi,hv]
  · exact ⟨by vsimp [chooseFactor,chooseProduct,hc.z],
      by vsimp [chooseFactor,chooseProduct,hc.one],by vsimp [chooseFactor,chooseProduct,hc.two]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

end NearQuarticWires.StageCert.Tokens
