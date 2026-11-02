import Proof.Quartic.StageColumns.Codeword

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def divisionScratch : List (Fin VV) :=
  [columnBlock, columnData, coordinateBlock, coordinateData]

/-- `imp:partition`, paper/paper.tex: the actual
basis and half-coordinate positions are divided into their original
block indices and positions within the two canonical block dimensions. -/
def divisionProgram : St VV MM :=
  .seq (.op (.dm columnIndex dataWidth columnBlock columnData))
    (.op (.dm coordinateIndex 22 coordinateBlock coordinateData))

/-- `imp:partition` and `prop:time`, paper/paper.tex: two literal binary divisions produce the exact block
coordinates, preserving all original source fields and loop counters. -/
theorem divisionProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams) (j p : ℕ)
    (hj : a.env columnIndex = j) (hp : a.env coordinateIndex = p)
    (hd : a.env dataWidth = PrimT.C4Geo.dB P) (hb : a.env 22 = P.b)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C divisionProgram a 3 (fun b =>
      b.env columnBlock = j / PrimT.C4Geo.dB P ∧
      b.env columnData = j % PrimT.C4Geo.dB P ∧
      b.env coordinateBlock = p / P.b ∧ b.env coordinateData = p % P.b ∧
      b.sh = a.sh ∧ Fr a b divisionScratch) := by
  obtain ⟨hbN, _, hdB⟩ := StageHamming.block_dimensions_le P
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  have hdpos := PrimT.C4Geo.dB_pos P
  unfold divisionProgram
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_dm C columnIndex dataWidth columnBlock columnData a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hd]; exact hdpos) (by rw [hd]; omega)) ?_
  rintro b rfl
  let a1 := (a.set columnBlock (a.env columnIndex / a.env dataWidth)).set columnData
    (a.env columnIndex % a.env dataWidth)
  refine (hs_dm C coordinateIndex 22 coordinateBlock coordinateData a1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by vsimp [a1, hb]; exact P.b_pos) (by vsimp [a1, hb]; omega)).mono le_rfl ?_
  rintro b rfl
  refine ⟨by vsimp [a1, hj, hd], by vsimp [a1, hj, hd],
    by vsimp [a1, hp, hb], by vsimp [a1, hp, hb], rfl, ?_⟩
  exact (Fr.set a _ (by decide)).trans ((Fr.set _ _ (by decide)).trans
    ((Fr.set a1 _ (by decide)).trans (Fr.set _ _ (by decide))))

end NearQuarticWires.StageColumns
