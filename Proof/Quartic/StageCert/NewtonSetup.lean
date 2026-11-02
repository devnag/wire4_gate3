import Proof.Quartic.StageCert.NewtonCapacity

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the original
population cutoff used by the exact Newton coefficient. -/
def newtonTau : Fin VV := ⟨99,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the coefficient's
actual degree index, retained across exact binomial computation. -/
def newtonIndex : Fin VV := ⟨100,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the canonical
negative-sign bit of the original integer coefficient. -/
def newtonSignField : Fin VV := ⟨101,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the original
coefficient magnitude, stored and emitted in binary. -/
def newtonMagnitudeField : Fin VV := ⟨102,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the nonnegative
parity exponent of a nonvanishing Newton coefficient. -/
def newtonDifference : Fin VV := ⟨103,by decide⟩
/-- `lem:maskpoly`, paper/paper.tex: the unused quotient
of the exact parity division by two. -/
def newtonHalf : Fin VV := ⟨104,by decide⟩

/-- `lem:maskpoly`, paper/paper.tex: the positive
degree branch prepares the exact original choose arguments `(a-1,tau)`. -/
def prepareNewtonBinomial : St VV MM := .seq (.op (.copy chooseN newtonIndex))
  (.seq (.op (.sub chooseN v1)) (.op (.copy chooseR newtonTau)))

/-- `lem:maskpoly`, paper/paper.tex: preparing natural
choose arguments preserves every original coefficient input and source store. -/
theorem prepareNewtonBinomial_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (tau index : ℕ) (ht : a.env newtonTau=tau) (hi : a.env newtonIndex=index) (hpos : 0 < index) :
    Hs C prepareNewtonBinomial a 5 (fun z=>z.env chooseN=index-1 ∧ z.env chooseR=tau ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [chooseN,chooseR]) := by
  unfold prepareNewtonBinomial
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C chooseN newtonIndex a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C chooseN v1 _ (by decide)
    (by vsimp [chooseN]; rw [hc.one,hi]; omega)) ?_
  rintro d rfl
  refine (hs_copy C chooseR newtonTau _ (by decide)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,?_,?_⟩
  · vsimp [chooseN,chooseR,hc.one,hi]
  · vsimp [chooseN,chooseR,ht]
  · exact ⟨by vsimp [chooseN,chooseR,hc.z],by vsimp [chooseN,chooseR,hc.one],
      by vsimp [chooseN,chooseR,hc.two]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))

/-- `lem:maskpoly`, paper/paper.tex: the final
coefficient fields retain the exact choose magnitude and exponent parity. -/
def finishNewtonBinomial : St VV MM := .seq (.op (.copy newtonMagnitudeField chooseValue))
  (.seq (.op (.copy newtonDifference newtonIndex))
    (.seq (.op (.sub newtonDifference newtonTau))
      (.op (.dm newtonDifference v2 newtonHalf newtonSignField))))

/-- `lem:maskpoly`, paper/paper.tex: canonical binary
coefficient fields are formed by exact natural arithmetic before any modulus. -/
theorem finishNewtonBinomial_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (tau index : ℕ) (ht : a.env newtonTau=tau) (hi : a.env newtonIndex=index)
    (hv : a.env chooseValue=(index-1).choose tau) (hle : tau ≤ index) (hW : 2≤C.Wd) :
    Hs C finishNewtonBinomial a 7 (fun z=>
      z.env newtonMagnitudeField=(index-1).choose tau ∧
      z.env newtonSignField=(index-tau)%2 ∧ z.sh=a.sh ∧ Cst z ∧
      Fr a z [newtonMagnitudeField,newtonDifference,newtonHalf,newtonSignField]) := by
  have hp : 4≤2^C.Wd := by
    have h := Nat.pow_le_pow_right (show 1≤(2:ℕ) by decide) hW
    norm_num at h
    exact h
  unfold finishNewtonBinomial
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_copy C newtonMagnitudeField chooseValue a (by decide)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C newtonDifference newtonIndex _ (by decide)) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C newtonDifference newtonTau _ (by decide)
    (by vsimp [newtonMagnitudeField,newtonDifference]; rw [ht,hi]; exact hle)) ?_
  rintro e rfl
  refine (hs_dm C newtonDifference v2 newtonHalf newtonSignField _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by vsimp [newtonMagnitudeField,newtonDifference,hc.two])
    (by vsimp [newtonMagnitudeField,newtonDifference,hc.two]; exact hp)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,?_,?_⟩
  · vsimp [newtonMagnitudeField,newtonDifference,newtonHalf,newtonSignField,hv]
  · vsimp [newtonMagnitudeField,newtonDifference,newtonHalf,newtonSignField,ht,hi,hc.two]
  · exact ⟨by vsimp [newtonMagnitudeField,newtonDifference,newtonHalf,newtonSignField,hc.z],
      by vsimp [newtonMagnitudeField,newtonDifference,newtonHalf,newtonSignField,hc.one],
      by vsimp [newtonMagnitudeField,newtonDifference,newtonHalf,newtonSignField,hc.two]⟩
  · exact (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans
      ((Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))))

end NearQuarticWires.StageCert.Tokens
