import Proof.Quartic.StageCert.DigitRate

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `eq:testE` and `lem:print`, paper/paper.tex: the exact predecessor-rate product is computed in binary. -/
def linearProduct : Fin VV := ⟨116,by decide⟩

/-- `eq:testE` and `lem:print`, paper/paper.tex: multiply the actual predecessor bit by its retained integer
rate before serializing the original signed coefficient. -/
def scaleDigitNegative : St VV MM :=
  .seq (.op (.mul linearNegative linearRate linearProduct))
    (.op (.copy linearNegative linearProduct))

/-- `eq:testE`, `lem:print` and `prop:time`, paper/paper.tex: exact binary scaling retains the source
and positive term; its width depends only on the actual integer rate
because every predecessor record is a Boolean bit. -/
theorem scaleDigitNegative_run (C : Ctx) (negative rate : ℕ)
    (a : DS VV MM) (hc : Cst a) (hn : a.env linearNegative=negative)
    (hr : a.env linearRate=rate) (hbit : negative≤1) (hfit : rate<2^C.Wd) :
    Hs C scaleDigitNegative a 3 (fun z=>
      z.env linearNegative=negative*rate ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [linearNegative,linearProduct]) := by
  have hproduct : negative*rate<2^C.Wd := by
    have hh : negative*rate≤rate := by nlinarith
    omega
  unfold scaleDigitNegative
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_mul C linearNegative linearRate linearProduct a (by decide) (by decide) (by decide)
      (by rw [hn,hr]; exact hproduct)) ?_
  rintro b rfl
  refine (hs_copy C linearNegative linearProduct _ (by decide)).mono le_rfl ?_
  rintro z rfl
  exact ⟨by vsimp [hn,hr],rfl,
    Cst.of_fr (T := [linearNegative,linearProduct]) hc
      ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))) (by decide),
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩

end NearQuarticWires.StageCert.Tokens
