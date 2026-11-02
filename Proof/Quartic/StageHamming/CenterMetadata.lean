import Proof.Quartic.StageHamming.Bounds

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def centerOutput : Fin VV := 118
def centerHalf : Fin VV := dataTarget
def centerLeft : Fin VV := dataIndex
def centerBlocked : Fin VV := dataCount
def centerFree : Fin VV := dataAnswer
def centerLocal : Fin VV := 127

def centerScratch : List (Fin VV) :=
  [vJ, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
    109, 110, 111, 112, 113, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

def centerMetadataScratch : List (Fin VV) :=
  [centerHalf, centerLeft, centerBlocked, centerFree, centerOutput,
    dataLimit, parityWidth, encoderLimit]

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: the exact block boundaries and data dimension
computed from the retained original partition parameters. -/
structure CenterReady (a : DS VV MM) (P : StarParams) : Prop where
  half : a.env centerHalf = P.r / 2
  left : a.env centerLeft = P.r / 2 * P.b
  blocked : a.env centerBlocked = P.r * P.b
  free : a.env centerFree = PrimT.C4Geo.hL P
  upper : a.env centerOutput = P.r * P.b + PrimT.C4Geo.hL P
  blockSize : a.env dataLimit = P.b
  parity : a.env parityWidth = P.s
  dataDimension : a.env encoderLimit = PrimT.C4Geo.dB P

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: all scalar center boundaries and dimensions are
physically derived from the actual original point metadata. -/
def centerMetadata : St VV MM :=
  .seq (.op (.copy centerHalf 21))
    (.seq (.op (.half centerHalf))
      (.seq (.op (.mul centerHalf 22 centerLeft))
        (.seq (.op (.mul 21 22 centerBlocked))
          (.seq (.op (.copy centerFree 20))
            (.seq (.op (.sub centerFree centerBlocked))
              (.seq (.op (.inc centerFree))
                (.seq (.op (.half centerFree))
                  (.seq (.op (.copy centerOutput centerBlocked))
                    (.seq (.op (.add centerOutput centerFree))
                      (.seq (.op (.copy dataLimit 22))
                        (.seq (.op (.copy parityWidth 23))
                          (.seq (.op (.copy encoderLimit 22))
                            (.op (.sub encoderLimit 23))))))))))))))

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: the exact center metadata is
constructed with an explicit constant source clock and the original
point producer's binary width, retaining every input parameter. -/
theorem centerMetadata_spec {C : Ctx} (a : DS VV MM) (P : StarParams)
    (hn : a.env 20 = P.n) (hr : a.env 21 = P.r)
    (hb : a.env 22 = P.b) (hs : a.env 23 = P.s)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C centerMetadata a 40 (fun b =>
      CenterReady b P ∧ b.sh = a.sh ∧ Fr a b centerMetadataScratch) := by
  have hsmall := scalar_word_bound P C.Wd hwidth
  have hblocked := P.r_mul_b_le
  have hleft : P.r / 2 * P.b ≤ P.n :=
    (Nat.mul_le_mul_right P.b (Nat.div_le_self P.r 2)).trans hblocked
  have hfree : PrimT.C4Geo.hL P ≤ P.n := by
    have hn8 : 8 ≤ P.n := by have h := P.two_le_r; have h' := P.four_r_le_n; omega
    unfold PrimT.C4Geo.hL
    omega
  have hleftW : P.r / 2 * P.b < 2 ^ C.Wd := by omega
  have hblockedW : P.r * P.b < 2 ^ C.Wd := by omega
  have hincW : P.n - P.r * P.b + 1 < 2 ^ C.Wd := by omega
  have hupperW : P.r * P.b + PrimT.C4Geo.hL P < 2 ^ C.Wd := by omega
  have hsB := (block_dimensions_le P).2.1
  unfold centerMetadata
  refine Hx.hs (Hs.then (hs_copy C centerHalf 21 a (by decide))
    (fun b hb' n1 hn1 => ?_))
  subst hb'
  let a1 := a.set centerHalf (a.env 21)
  refine Hs.then (hs_half C centerHalf a1) (fun b hb' n2 hn2 => ?_)
  subst hb'
  let a2 := a1.set centerHalf (a1.env centerHalf / 2)
  refine Hs.then (hs_mul C centerHalf 22 centerLeft a2 (by decide) (by decide) (by decide)
    (by simpa (config := { decide := true }) [a2, a1, DS.set, hr, hb] using hleftW))
    (fun b hb' n3 hn3 => ?_)
  subst hb'
  let a3 := a2.set centerLeft (a2.env centerHalf * a2.env 22)
  refine Hs.then (hs_mul C 21 22 centerBlocked a3 (by decide) (by decide) (by decide)
    (by simpa (config := { decide := true }) [a3, a2, a1, DS.set, hr, hb] using hblockedW))
    (fun b hb' n4 hn4 => ?_)
  subst hb'
  let a4 := a3.set centerBlocked (a3.env 21 * a3.env 22)
  refine Hs.then (hs_copy C centerFree 20 a4 (by decide)) (fun b hb' n5 hn5 => ?_)
  subst hb'
  let a5 := a4.set centerFree (a4.env 20)
  refine Hs.then (hs_sub C centerFree centerBlocked a5 (by decide)
    (by simpa (config := { decide := true }) [a5, a4, a3, a2, a1, DS.set, hn, hr, hb]
      using hblocked)) (fun b hb' n6 hn6 => ?_)
  subst hb'
  let a6 := a5.set centerFree (a5.env centerFree - a5.env centerBlocked)
  refine Hs.then (hs_inc C centerFree a6
    (by simpa (config := { decide := true }) [a6, a5, a4, a3, a2, a1, DS.set, hn, hr, hb]
      using hincW)) (fun b hb' n7 hn7 => ?_)
  subst hb'
  let a7 := a6.set centerFree (a6.env centerFree + 1)
  refine Hs.then (hs_half C centerFree a7) (fun b hb' n8 hn8 => ?_)
  subst hb'
  let a8 := a7.set centerFree (a7.env centerFree / 2)
  refine Hs.then (hs_copy C centerOutput centerBlocked a8 (by decide))
    (fun b hb' n9 hn9 => ?_)
  subst hb'
  let a9 := a8.set centerOutput (a8.env centerBlocked)
  refine Hs.then (hs_add C centerOutput centerFree a9 (by decide)
    (by simpa (config := { decide := true })
      [a9, a8, a7, a6, a5, a4, a3, a2, a1, DS.set, hn, hr, hb, PrimT.C4Geo.hL]
      using hupperW)) (fun b hb' n10 hn10 => ?_)
  subst hb'
  let a10 := a9.set centerOutput (a9.env centerOutput + a9.env centerFree)
  refine Hs.then (hs_copy C dataLimit 22 a10 (by decide)) (fun b hb' n11 hn11 => ?_)
  subst hb'
  let a11 := a10.set dataLimit (a10.env 22)
  refine Hs.then (hs_copy C parityWidth 23 a11 (by decide)) (fun b hb' n12 hn12 => ?_)
  subst hb'
  let a12 := a11.set parityWidth (a11.env 23)
  refine Hs.then (hs_copy C encoderLimit 22 a12 (by decide)) (fun b hb' n13 hn13 => ?_)
  subst hb'
  let a13 := a12.set encoderLimit (a12.env 22)
  refine Hs.last (hs_sub C encoderLimit 23 a13 (by decide)
    (by simpa (config := { decide := true })
      [a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, DS.set, hs, hb]
      using hsB)) ?_
  rintro b rfl n14 hn14
  let a14 := a13.set encoderLimit (a13.env encoderLimit - a13.env 23)
  refine ⟨⟨?_, rfl, ?_⟩, by omega⟩
  · constructor <;> vsimp [a14, a13, a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1,
      hn, hr, hb, hs, PrimT.C4Geo.hL, PrimT.C4Geo.dB]
  · exact (Fr.set a _ (by decide)).trans ((Fr.set a1 _ (by decide)).trans
      ((Fr.set a2 _ (by decide)).trans ((Fr.set a3 _ (by decide)).trans
      ((Fr.set a4 _ (by decide)).trans ((Fr.set a5 _ (by decide)).trans
      ((Fr.set a6 _ (by decide)).trans ((Fr.set a7 _ (by decide)).trans
      ((Fr.set a8 _ (by decide)).trans ((Fr.set a9 _ (by decide)).trans
      ((Fr.set a10 _ (by decide)).trans ((Fr.set a11 _ (by decide)).trans
      ((Fr.set a12 _ (by decide)).trans (Fr.set a13 _ (by decide))))))))))))))

end NearQuarticWires.StageHamming
