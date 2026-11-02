import Proof.Quartic.StagePullback.SideCount
import Proof.Quartic.StagePullback.Side

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.NativeRows

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def nativeWidth : Fin VV := 37
def outputIndex : Fin VV := 38
def leftCount : Fin VV := 39
def rightCount : Fin VV := 40
def countTemporary : Fin VV := 41

/-- `imp:partition`, paper/paper.tex: the shared
native Hamming width is at most the original dimension. -/
theorem nativeWidth_le (P : StarParams) : PrimT.C4Geo.width P ≤ P.n := by
  have hhalf : P.r / 2 * P.b ≤ P.r * P.b :=
    Nat.mul_le_mul_right _ (Nat.div_le_self P.r 2)
  have hfree := PrimT.C4Geo.hL_le P
  unfold PrimT.C4Geo.width
  omega

/-- `imp:pullback`, paper/paper.tex: physically
compute the native half width from the actual original-coordinate side
boundaries, including its free-coordinate padding. -/
def nativeWidthProgram : St VV MM :=
  .seq (.op (.copy nativeWidth Sides.freeLeftEnd))
    (.seq (.op (.sub nativeWidth Sides.blockedEnd)) (.op (.add nativeWidth Sides.leftEnd)))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the actual side boundaries produce the exact shared
native Hamming width with three paid binary operations. -/
theorem nativeWidthProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (hl : a.env Sides.leftEnd = P.r / 2 * P.b) (hb : a.env Sides.blockedEnd = P.r * P.b)
    (hf : a.env Sides.freeLeftEnd = P.r * P.b + PrimT.C4Geo.hL P)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C nativeWidthProgram a 5 (fun b => b.env nativeWidth = PrimT.C4Geo.width P ∧
      b.sh = a.sh ∧ Fr a b [nativeWidth]) := by
  have hn := (Flips.markerWidth C P hwidth).2.2.2
  unfold nativeWidthProgram
  refine Hx.hs (Hs.then (hs_copy C nativeWidth Sides.freeLeftEnd a (by decide))
    (fun b he n1 hn1 => ?_))
  subst he
  refine Hs.then (hs_sub C nativeWidth Sides.blockedEnd _ (by decide)
    (by vsimp [hf, hb])) (fun b he n2 hn2 => ?_)
  subst he
  refine Hs.last (hs_add C nativeWidth Sides.leftEnd _ (by decide) (by
    vsimp [hf, hb, hl]
    have h := nativeWidth_le P
    unfold PrimT.C4Geo.width at h
    omega)) ?_
  rintro b he n3 hn3
  subst he
  refine ⟨⟨?_, rfl, (Fr.set a _ (by simp)).trans
    ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩, by omega⟩
  vsimp [hf, hb, hl, PrimT.C4Geo.width, Nat.add_comm]

/-- `imp:pullback`, paper/paper.tex: physically
compute the two row lengths and exchange them for the certificate's
transposed column order. -/
def countsProgram : St VV MM :=
  .seq (.op (.copy rightCount 20)) (.seq (.op (.sub rightCount nativeWidth))
    (.seq (.op (.copy leftCount nativeWidth))
      (.ite (.eq transposeFlag v1)
        (.seq (.op (.copy countTemporary leftCount))
          (.seq (.op (.copy leftCount rightCount)) (.op (.copy rightCount countTemporary)))) skipS)))

/-- `imp:pullback` and `prop:time`, paper/paper.tex: actual geometry and the physical transpose bit determine
the two exact native row lengths; no supplied coordinate map is read. -/
theorem countsProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (transpose : Bool)
    (hc : Cst a) (hn : a.env 20 = P.n) (hw : a.env nativeWidth = PrimT.C4Geo.width P)
    (ht : a.env transposeFlag = transpose.toNat) :
    Hs C countsProgram a 16 (fun b =>
      b.env leftCount = (if transpose then P.n - PrimT.C4Geo.width P else PrimT.C4Geo.width P) ∧
      b.env rightCount = (if transpose then PrimT.C4Geo.width P else P.n - PrimT.C4Geo.width P) ∧
      b.sh = a.sh ∧ Fr a b [leftCount, rightCount, countTemporary, vJ]) := by
  unfold countsProgram
  refine Hx.hs (Hs.then (hs_copy C rightCount 20 a (by decide)) (fun b he n1 hn1 => ?_))
  subst he
  refine Hs.then (hs_sub C rightCount nativeWidth _ (by decide)
    (by vsimp [hn, hw]; exact nativeWidth_le P)) (fun b he n2 hn2 => ?_)
  subst he
  refine Hs.then (hs_copy C leftCount nativeWidth _ (by decide)) (fun b he n3 hn3 => ?_)
  subst he
  let b := ((a.set rightCount (a.env 20)).set rightCount
    (a.env 20 - a.env nativeWidth)).set leftCount (a.env nativeWidth)
  have hb0 : b.env leftCount = PrimT.C4Geo.width P := by simp [b, hw]
  have hb1 : b.env rightCount = P.n - PrimT.C4Geo.width P := by
    simp only [b, DS.set_env_ne _ _ (by decide : rightCount ≠ leftCount), DS.set_env_self, hn, hw]
  have hbf : Fr a b [leftCount, rightCount, countTemporary, vJ] :=
    (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  have hbc : Cst b := hc.of_fr hbf (by decide)
  have hbt : b.env transposeFlag = transpose.toNat := (hbf _ (by decide)).trans ht
  have hbranch : Hs C
      (.ite (.eq transposeFlag v1)
        (.seq (.op (.copy countTemporary leftCount))
          (.seq (.op (.copy leftCount rightCount)) (.op (.copy rightCount countTemporary)))) skipS)
      b 6 (fun c =>
        c.env leftCount = (if transpose then P.n - PrimT.C4Geo.width P else PrimT.C4Geo.width P) ∧
        c.env rightCount = (if transpose then PrimT.C4Geo.width P else P.n - PrimT.C4Geo.width P) ∧
        c.sh = b.sh ∧ Fr b c [leftCount, rightCount, countTemporary, vJ]) := by
    cases transpose with
    | false =>
      refine Hs.mono (Hs.iteF (show transposeFlag ≠ v1 by decide)
        (by simp [Cnd.eval, hbt, hbc.one]) (skip_spec b)) (by omega) ?_
      rintro c rfl
      exact ⟨by simpa only [Bool.false_eq_true, if_false, DS.set_env_ne _ _ (by decide : leftCount ≠ vJ)] using hb0,
        by simpa only [Bool.false_eq_true, if_false, DS.set_env_ne _ _ (by decide : rightCount ≠ vJ)] using hb1,
        rfl, Fr.set b _ (by simp)⟩
    | true =>
      refine Hs.iteT (show transposeFlag ≠ v1 by decide) (by simp [Cnd.eval, hbt, hbc.one]) ?_
      refine Hx.hs (Hs.then (hs_copy C countTemporary leftCount b (by decide))
        (fun c he n4 hn4 => ?_))
      subst he
      refine Hs.then (hs_copy C leftCount rightCount _ (by decide)) (fun c he n5 hn5 => ?_)
      subst he
      refine Hs.last (hs_copy C rightCount countTemporary _ (by decide)) ?_
      rintro c he n6 hn6
      subst he
      refine ⟨⟨?_, ?_, rfl, (Fr.set b _ (by simp)).trans
        ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))⟩, by omega⟩
      · vsimp [hb1]
      · vsimp [hb0]
  refine Hs.last hbranch ?_
  rintro c ⟨hl, hr, hsh, hfr⟩ n4 hn4
  exact ⟨⟨hl, hr, hsh, hbf.trans hfr⟩, by omega⟩

end NearQuarticWires.StagePullback.NativeRows
