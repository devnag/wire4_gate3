import Proof.Quartic.StageCert.IncidenceAt

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires

/-- `imp:partition` and `def:mask`, paper/paper.tex: the remaining pattern code is decoded least-significant first. -/
def patternCode : Fin VV := ⟨100,by decide⟩
/-- `imp:partition`, paper/paper.tex: the exact radix `b+1`. -/
def patternRadix : Fin VV := ⟨101,by decide⟩
/-- `imp:partition`, paper/paper.tex: the actual block size. -/
def patternBlockSize : Fin VV := ⟨102,by decide⟩
/-- `def:mask`, paper/paper.tex: the original block index. -/
def patternBlock : Fin VV := ⟨103,by decide⟩
/-- `def:mask`, paper/paper.tex: the endpoint of one side. -/
def patternEnd : Fin VV := ⟨104,by decide⟩
/-- `imp:partition`, paper/paper.tex: one exact pattern digit. -/
def patternDigit : Fin VV := ⟨105,by decide⟩
/-- `imp:partition`, paper/paper.tex: the quotient after a digit. -/
def patternQuotient : Fin VV := ⟨106,by decide⟩
/-- `def:mask`, paper/paper.tex: the accumulated side flag. -/
def patternFlag : Fin VV := ⟨107,by decide⟩

/-- `imp:partition`, paper/paper.tex: one physical base-`b+1`
digit is extracted and removed from the remaining code. -/
def nextPatternDigit : St VV :=
  .seq (.op (.dm patternCode patternRadix patternQuotient patternDigit))
    (.op (.copy patternCode patternQuotient))

/-- `imp:partition`, paper/paper.tex: exact quotient/remainder
semantics with constant arithmetic-operation cost. -/
theorem nextPatternDigit_run (C : Ctx) (a : DS VV)
    (hq : 0<a.env patternRadix) (hfit : 2*a.env patternRadix≤2^C.Wd) :
    Hs C nextPatternDigit a 3 (fun b =>
      b.env patternCode=a.env patternCode/a.env patternRadix ∧
      b.env patternDigit=a.env patternCode%a.env patternRadix ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧
      Fr a b [patternCode,patternQuotient,patternDigit]) := by
  unfold nextPatternDigit
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_dm C patternCode patternRadix patternQuotient patternDigit a
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq hfit) ?_
  rintro b rfl
  refine (hs_copy C patternCode patternQuotient _ (by decide)).mono le_rfl ?_
  rintro d rfl
  exact ⟨by simp [DS.set,patternCode,patternDigit,patternQuotient],
    by simp [DS.set,patternCode,patternDigit,patternQuotient],rfl,rfl,rfl,
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩

/-- `def:mask`, paper/paper.tex: a nonzero pattern digit
selects the original coordinate `block*b+digit-1`. -/
def setPatternCoordinate : St VV :=
  .seq (.op (.sub patternDigit v1))
    (.seq (.op (.mul patternBlock patternBlockSize coordinate))
      (.op (.add coordinate patternDigit)))

/-- `def:mask`, paper/paper.tex: the selected coordinate
is computed by actual binary subtraction, multiplication and addition. -/
theorem setPatternCoordinate_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (hd : 1≤a.env patternDigit)
    (hfit : a.env patternBlock*a.env patternBlockSize+(a.env patternDigit-1)<2^C.Wd) :
    Hs C setPatternCoordinate a 5 (fun b =>
      b.env coordinate=a.env patternBlock*a.env patternBlockSize+(a.env patternDigit-1) ∧
      b.cp=a.cp ∧ b.wq=a.wq ∧ b.out=a.out ∧
      Fr a b [coordinate,patternDigit]) := by
  unfold setPatternCoordinate
  refine Hs.seq (t1 := 1) (t2 := 3)
    (hs_sub C patternDigit v1 a (by decide) (by rw [hc.one]; exact hd)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_mul C patternBlock patternBlockSize coordinate _ (by decide) (by decide) (by decide)
      (by simp only [DS.set_env_ne _ _ (by decide : patternBlock≠patternDigit),
        DS.set_env_ne _ _ (by decide : patternBlockSize≠patternDigit)]; omega)) ?_
  rintro d rfl
  refine (hs_add C coordinate patternDigit _ (by decide) (by
    simp only [DS.set_env_self,DS.set_env_ne _ _ (by decide : patternDigit≠coordinate),
      DS.set_env_ne _ _ (by decide : patternBlock≠patternDigit),
      DS.set_env_ne _ _ (by decide : patternBlockSize≠patternDigit)]
    rw [hc.one]
    exact hfit)).mono le_rfl ?_
  rintro e rfl
  exact ⟨by simp [DS.set,hc.one,patternDigit,patternBlock,patternBlockSize,coordinate],rfl,rfl,rfl,
    (Fr.set _ _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩

end NearQuarticWires.StageCert.Incidence
