import Proof.Quartic.StageCert.PatternProgram

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch

/-- `def:mask`, paper/paper.tex: the first side's result
is retained while the second original pattern is scanned. -/
def patternLeftResult : Fin VV := ⟨111,by decide⟩
/-- `def:mask`, paper/paper.tex: the canonical left error
pattern code of the current cell entry. -/
def patternLeftInput : Fin VV := ⟨112,by decide⟩
/-- `def:mask`, paper/paper.tex: the canonical right error
pattern code of the same cell entry. -/
def patternRightInput : Fin VV := ⟨113,by decide⟩

/-- `def:mask`, paper/paper.tex: a side begins at original
block zero on the left and at the side-slot count on the right. -/
def preparePatternSide (right : Bool) : St VV :=
  .seq (.op (.copy patternOffset (if right then patternCount else vZ)))
    (.op (.copy patternInput (if right then patternRightInput else patternLeftInput)))

/-- `def:mask`, paper/paper.tex: the side's source pattern
and original block offset are copied without changing any other public field. -/
theorem preparePatternSide_run (C : Ctx) (a : DS VV) (hc : Cst a) (right : Bool) :
    Hs C (preparePatternSide right) a 3 (fun z =>
      z.env patternOffset=(if right then a.env patternCount else 0) ∧
      z.env patternInput=(if right then a.env patternRightInput else a.env patternLeftInput) ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z [patternOffset,patternInput]) := by
  unfold preparePatternSide
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_copy C patternOffset (if right then patternCount else vZ) a (by cases right <;> decide)) ?_
  rintro b rfl
  refine (hs_copy C patternInput (if right then patternRightInput else patternLeftInput) _
    (by cases right <;> decide)).mono le_rfl ?_
  rintro z rfl
  refine ⟨?_,?_,rfl,rfl,rfl,?_,?_⟩
  · cases right <;> vsimp [patternOffset,patternInput,patternCount,patternLeftInput,patternRightInput,hc.z]
  · cases right <;> vsimp [patternOffset,patternInput,patternCount,patternLeftInput,patternRightInput]
  · refine ⟨?_,?_,?_,?_⟩
    · cases right <;> vsimp [patternOffset,patternInput,patternCount,patternLeftInput,patternRightInput,hc.z]
    · cases right <;> vsimp [patternOffset,patternInput,patternCount,patternLeftInput,patternRightInput,hc.one]
    · cases right <;> vsimp [patternOffset,patternInput,patternCount,patternLeftInput,patternRightInput,hc.two]
    · cases right <;> vsimp [patternOffset,patternInput,patternCount,patternLeftInput,patternRightInput,hc.pos]
  · exact (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))

/-- `def:mask`, paper/paper.tex: the structural entry is
accepted when either original side avoids all heavy coordinates. -/
def combinePatternSides : St VV :=
  .ite (.eq patternFlag vZ) (.op (.copy patternFlag patternLeftResult)) skipS

/-- `def:mask`, paper/paper.tex: the physical final side
combination is exactly Boolean OR, with no approximation of either side. -/
theorem combinePatternSides_run (C : Ctx) (a : DS VV) (hc : Cst a)
    (left right : Bool) (hl : a.env patternLeftResult=left.toNat)
    (hr : a.env patternFlag=right.toNat) :
    Hs C combinePatternSides a 2 (fun z =>
      z.env patternFlag=(left || right).toNat ∧
      z.cp=a.cp ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧ Fr a z [patternFlag,vJ]) := by
  unfold combinePatternSides
  refine Hs.ite (c := .eq patternFlag vZ) (show patternFlag≠vZ by decide) ?_ ?_
  · intro he
    have hright : right=false := by cases right <;> simp_all [Cnd.eval,Bool.toNat,hc.z]
    refine (hs_copy C patternFlag patternLeftResult a (by decide)).mono le_rfl ?_
    rintro z rfl
    refine ⟨by simp [hl,hright],rfl,rfl,rfl,?_,Fr.set _ _ (by simp)⟩
    exact Cst.of_fr hc (Fr.set (T := [patternFlag]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  · intro he
    have hright : right=true := by cases right <;> simp_all [Cnd.eval,Bool.toNat,hc.z]
    refine (skip_spec a).mono le_rfl ?_
    rintro z rfl
    refine ⟨by rw [DS.set_env_ne _ _ (by decide),hr]; simp [hright],rfl,rfl,rfl,?_,Fr.set _ _ (by simp)⟩
    exact Cst.of_fr hc (Fr.set (T := [vJ]) _ _ (by simp)) (by decide)
      (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)

end NearQuarticWires.StageCert.Incidence
