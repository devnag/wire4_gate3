import Proof.Gates.Cells.Kit
import Proof.Gates.Cells.Comp
import Proof.Gates.WordPrograms.SInt

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: the sign,
magnitude, positive threshold and acceptance registers of a strict test. -/
def testSign : Fin VV := ⟨40, by decide⟩
def testMagnitude : Fin VV := ⟨41, by decide⟩
def testBound : Fin VV := ⟨42, by decide⟩
def testAccept : Fin VV := ⟨43, by decide⟩

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: a signed integer
is below a natural threshold precisely by its sign and magnitude. -/
theorem strictTest_iff (z : ℤ) (R : ℕ) :
    z < (R : ℤ) ↔ z < 0 ∨ z.natAbs < R := by
  omega

/-- `sec:algorithm`, paper/paper.tex: the physical strict-test
instruction preserves acceptance on a passing record and clears it otherwise. -/
def strictTest : St VV MM :=
  .ite (.eq testSign vZ)
    (.ite (.lt testMagnitude testBound) skipS (.op (.zero testAccept)))
    skipS

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: the strict-test
instruction implements conjunction with the literal signed inequality. -/
theorem strictTest_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ) (R : ℕ)
    (hs : a.env testSign = if z < 0 then 1 else 0)
    (hm : a.env testMagnitude = z.natAbs) (hR : a.env testBound = R) :
    Hs C strictTest a 3 (fun b =>
      b.env testAccept = (if z < (R : ℤ) then a.env testAccept else 0) ∧
      b.sh = a.sh ∧ Fr a b [vJ, testAccept]) := by
  classical
  have hzero : a.env vZ = 0 := hc.z
  unfold strictTest
  by_cases hz : z < 0
  · have hx : Cnd.eval a (.eq testSign vZ) = false := by simp [Cnd.eval, hs, hz, hzero]
    refine (Hs.iteF (by norm_num [Cnd.wf, testSign, vZ]) hx (skip_spec a)).mono (by omega) ?_
    intro b hb
    subst b
    have hzR : z < (R : ℤ) := lt_of_lt_of_le hz (Int.natCast_nonneg R)
    simp [hzR, DS.sh, testAccept, vJ, DS.set, Fr]
    intro y hy _
    exact Function.update_of_ne hy _ _
  · have hx : Cnd.eval a (.eq testSign vZ) = true := by simp [Cnd.eval, hs, hz, hzero]
    by_cases hr : z.natAbs < R
    · have hy : Cnd.eval a (.lt testMagnitude testBound) = true := by simp [Cnd.eval, hm, hR, hr]
      refine (Hs.iteT (by norm_num [Cnd.wf, testSign, vZ]) hx (Hs.iteT (by norm_num [Cnd.wf, testMagnitude, testBound]) hy (skip_spec a))).mono (by omega) ?_
      intro b hb
      subst b
      have hzR : z < (R : ℤ) := (strictTest_iff z R).mpr (Or.inr hr)
      simp [hzR, DS.sh, testAccept, vJ, DS.set, Fr]
      intro y hy _
      exact Function.update_of_ne hy _ _
    · have hy : Cnd.eval a (.lt testMagnitude testBound) = false := by simp [Cnd.eval, hm, hR, hr]
      refine (Hs.iteT (by norm_num [Cnd.wf, testSign, vZ]) hx (Hs.iteF (by norm_num [Cnd.wf, testMagnitude, testBound]) hy (hs_zero C testAccept a))).mono (by omega) ?_
      intro b hb
      subst b
      have hzR : ¬ z < (R : ℤ) := by rw [strictTest_iff]; tauto
      simp [hzR, DS.sh, DS.set, Fr]
      intro y _ hy
      exact Function.update_of_ne hy _ _

end NearQuarticWires.StageCert
