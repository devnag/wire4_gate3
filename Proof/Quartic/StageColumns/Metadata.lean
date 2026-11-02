import Proof.Quartic.StageColumns.Bit
import Proof.Quartic.StageHamming.CenterMetadata

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

structure Prepared (a : DS VV MM) (P : StarParams) : Prop where
  constants : Cst a
  blockWidth : a.env 22 = P.b
  parityWidth : a.env 23 = P.s
  width : a.env nativeWidth = PrimT.C4Geo.width P
  dimension : a.env dimension = PrimT.C4Geo.dRow P
  left : a.env leftWidth = P.r / 2 * P.b
  data : a.env dataWidth = PrimT.C4Geo.dB P
  count : a.env dataCount = P.r / 2 * PrimT.C4Geo.dB P

def metadataScratch : List (Fin VV) :=
  StageHamming.centerMetadataScratch ++ [halfCount, leftWidth, dataWidth, dataCount,
    nativeWidth, dimension]

def metadataProgram : St VV MM :=
  .seq StageHamming.centerMetadata
    (.seq (.op (.copy halfCount StageHamming.centerHalf))
      (.seq (.op (.copy leftWidth StageHamming.centerLeft))
        (.seq (.op (.copy dataWidth StageHamming.encoderLimit))
          (.seq (.op (.mul halfCount dataWidth dataCount))
            (.seq (.op (.copy nativeWidth StageHamming.centerFree))
              (.seq (.op (.copy dimension nativeWidth))
                (.seq (.op (.add nativeWidth leftWidth))
                  (.op (.add dimension dataCount)))))))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: all column dimensions are physically constructed from
the four original partition parameters with a constant source clock. -/
theorem metadataProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (hc : Cst a) (hn : a.env 20 = P.n) (hr : a.env 21 = P.r)
    (hb : a.env 22 = P.b) (hs : a.env 23 = P.s) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C metadataProgram a 70 (fun b =>
      Prepared b P ∧ b.sh = a.sh ∧ Fr a b metadataScratch) := by
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  have hleft : P.r / 2 * P.b ≤ P.n :=
    (Nat.mul_le_mul_right P.b (Nat.div_le_self P.r 2)).trans P.r_mul_b_le
  have hdata : P.r / 2 * PrimT.C4Geo.dB P ≤ P.n :=
    (Nat.mul_le_mul_left (P.r / 2) (StageHamming.block_dimensions_le P).2.2).trans hleft
  have hdims := dimensions_le P
  unfold metadataProgram
  refine Hx.hs (Hs.then (StageHamming.centerMetadata_spec a P hn hr hb hs hwidth)
    (fun b ⟨hready, hsh, hf⟩ n0 hn0 => ?_))
  refine Hs.then (hs_copy C halfCount StageHamming.centerHalf b (by decide))
    (fun c he n1 hn1 => ?_)
  subst he
  let a1 := b.set halfCount (b.env StageHamming.centerHalf)
  refine Hs.then (hs_copy C leftWidth StageHamming.centerLeft a1 (by decide))
    (fun c he n2 hn2 => ?_)
  subst he
  let a2 := a1.set leftWidth (a1.env StageHamming.centerLeft)
  refine Hs.then (hs_copy C dataWidth StageHamming.encoderLimit a2 (by decide))
    (fun c he n3 hn3 => ?_)
  subst he
  let a3 := a2.set dataWidth (a2.env StageHamming.encoderLimit)
  refine Hs.then (hs_mul C halfCount dataWidth dataCount a3
    (by decide) (by decide) (by decide) (by
      vsimp [a3, a2, a1, hready.half, hready.dataDimension]; omega))
    (fun c he n4 hn4 => ?_)
  subst he
  let a4 := a3.set dataCount (a3.env halfCount * a3.env dataWidth)
  refine Hs.then (hs_copy C nativeWidth StageHamming.centerFree a4 (by decide))
    (fun c he n5 hn5 => ?_)
  subst he
  let a5 := a4.set nativeWidth (a4.env StageHamming.centerFree)
  refine Hs.then (hs_copy C dimension nativeWidth a5 (by decide))
    (fun c he n6 hn6 => ?_)
  subst he
  let a6 := a5.set dimension (a5.env nativeWidth)
  refine Hs.then (hs_add C nativeWidth leftWidth a6 (by decide) (by
    vsimp [a6, a5, a4, a3, a2, a1, hready.free, hready.left]
    have h : PrimT.C4Geo.hL P + P.r / 2 * P.b = PrimT.C4Geo.width P := by
      simp [PrimT.C4Geo.width, Nat.add_comm]
    rw [h]; omega)) (fun c he n7 hn7 => ?_)
  subst he
  let a7 := a6.set nativeWidth (a6.env nativeWidth + a6.env leftWidth)
  refine Hs.last (hs_add C dimension dataCount a7 (by decide) (by
    vsimp [a7, a6, a5, a4, a3, a2, a1, hready.free, hready.half, hready.dataDimension]
    have h : PrimT.C4Geo.hL P + P.r / 2 * PrimT.C4Geo.dB P = PrimT.C4Geo.dRow P := by
      simp [PrimT.C4Geo.dRow, StarParams.leftCenterBits, PrimT.C4Geo.dB, PrimT.C4Geo.hL, Nat.add_comm]
    rw [h]; omega)) ?_
  rintro c rfl n8 hn8
  let a8 := a7.set dimension (a7.env dimension + a7.env dataCount)
  have hbf : Fr b a8 metadataScratch :=
    (Fr.set b _ (by decide)).trans ((Fr.set a1 _ (by decide)).trans
      ((Fr.set a2 _ (by decide)).trans ((Fr.set a3 _ (by decide)).trans
        ((Fr.set a4 _ (by decide)).trans ((Fr.set a5 _ (by decide)).trans
          ((Fr.set a6 _ (by decide)).trans (Fr.set a7 _ (by decide))))))))
  have hab : Fr a a8 metadataScratch :=
    (hf.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans hbf
  refine ⟨⟨?_, hsh, hab⟩, by omega⟩
  refine ⟨hc.of_fr hab (by decide), (hab _ (by decide)).trans hb,
    (hab _ (by decide)).trans hs, ?_, ?_, ?_, ?_, ?_⟩
  all_goals vsimp [a8, a7, a6, a5, a4, a3, a2, a1, hready.free, hready.half,
    hready.left, hready.dataDimension, PrimT.C4Geo.width, PrimT.C4Geo.dRow, StarParams.leftCenterBits, PrimT.C4Geo.dB, PrimT.C4Geo.hL]
  all_goals omega

end NearQuarticWires.StageColumns
