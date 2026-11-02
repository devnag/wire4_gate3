import Proof.Quartic.StageColumns.Request

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def columnIndex : Fin VV := 80
def coordinateIndex : Fin VV := 81
def nativeWidth : Fin VV := 82
def dimension : Fin VV := 83
def halfCount : Fin VV := 84
def leftWidth : Fin VV := 85
def dataWidth : Fin VV := 86
def dataCount : Fin VV := 87
def columnBlock : Fin VV := 88
def columnData : Fin VV := 89
def coordinateBlock : Fin VV := 90
def coordinateData : Fin VV := 91
def freePosition : Fin VV := 92
def result : Fin VV := 93
def temporary : Fin VV := 94

def codewordScratch : List (Fin VV) :=
  [StageHamming.dataLimit, StageHamming.parityWidth, StageHamming.dataTarget,
    StageHamming.columnData, StageHamming.columnTarget, result] ++
    StageHamming.dataPositionScratch ++ StageHamming.columnBitScratch

/-- `imp:partition`, paper/paper.tex: scalar data
and codeword positions physically determine their canonical Hamming
column bit, with both initialization sequences included. -/
def codewordProgram : St VV MM :=
  .seq (.op (.copy StageHamming.dataLimit 22))
    (.seq (.op (.copy StageHamming.parityWidth 23))
      (.seq (.op (.copy StageHamming.dataTarget columnData))
        (.seq StageHamming.dataPosition
          (.seq (.op (.copy StageHamming.columnData StageHamming.dataAnswer))
            (.seq (.op (.copy StageHamming.columnTarget coordinateData))
              (.seq StageHamming.columnBit (.op (.copy result StageHamming.columnOutput))))))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: the actual data-position scan followed by the actual
parity scan returns the exact original canonical codeword bit. -/
theorem codewordProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (m q : ℕ)
    (hb : a.env 22 = P.b) (hs : a.env 23 = P.s)
    (hm : a.env columnData = m) (hq : a.env coordinateData = q)
    (hmB : m < PrimT.C4Geo.dB P) (hqB : q < P.b)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C codewordProgram a
      (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 60) (fun b =>
        b.env result = (PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P m) q).toNat ∧
        b.sh = a.sh ∧ Fr a b codewordScratch) := by
  obtain ⟨hbN, hsB, _⟩ := StageHamming.block_dimensions_le P
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  have hpow := P.b_succ
  have hdp := (PrimT.C4Geo.dpos_mem P m hmB).1
  unfold codewordProgram
  refine Hx.hs (Hs.then (hs_copy C StageHamming.dataLimit 22 a (by decide))
    (fun b hb' n1 hn1 => ?_))
  subst hb'
  let a1 := a.set StageHamming.dataLimit (a.env 22)
  refine Hs.then (hs_copy C StageHamming.parityWidth 23 a1 (by decide))
    (fun b hb' n2 hn2 => ?_)
  subst hb'
  let a2 := a1.set StageHamming.parityWidth (a1.env 23)
  refine Hs.then (hs_copy C StageHamming.dataTarget columnData a2 (by decide))
    (fun b hb' n3 hn3 => ?_)
  subst hb'
  let a3 := a2.set StageHamming.dataTarget (a2.env columnData)
  have hf3 : Fr a a3 codewordScratch :=
    (Fr.set a _ (by decide)).trans ((Fr.set a1 _ (by decide)).trans
      (Fr.set a2 _ (by decide)))
  have hc3 : Cst a3 := hc.of_fr hf3 (by decide)
  have hb3 : a3.env StageHamming.dataLimit = P.b := by vsimp [a3, a2, a1, hb]
  have hs3 : a3.env StageHamming.parityWidth = P.s := by vsimp [a3, a2, a1, hs]
  have hm3 : a3.env StageHamming.dataTarget = m := by vsimp [a3, a2, a1, hm]
  refine Hs.then (StageHamming.dataPosition_dpos_spec a3 hc3 P m hb3 hs3 hm3
    (by omega) (by omega) (by omega))
    (fun b ⟨hbv, hbsh, hbfr⟩ n4 hn4 => ?_)
  have hfb : Fr a b codewordScratch := hf3.trans (hbfr.weaken (by
    intro y hy
    exact List.mem_append_left _ (List.mem_append_right _ hy)))
  have hbc : Cst b := hc.of_fr hfb (by decide)
  have hbq : b.env coordinateData = q := (hfb _ (by decide)).trans hq
  refine Hs.then (hs_copy C StageHamming.columnData StageHamming.dataAnswer b (by decide))
    (fun d hd n5 hn5 => ?_)
  subst hd
  let a4 := b.set StageHamming.columnData (b.env StageHamming.dataAnswer)
  refine Hs.then (hs_copy C StageHamming.columnTarget coordinateData a4 (by decide))
    (fun d hd n6 hn6 => ?_)
  subst hd
  let a5 := a4.set StageHamming.columnTarget (a4.env coordinateData)
  have hf5 : Fr b a5 codewordScratch :=
    (Fr.set b _ (by decide)).trans (Fr.set a4 _ (by decide))
  have hc5 : Cst a5 := hbc.of_fr hf5 (by decide)
  have hi5 : a5.env StageHamming.columnData = PrimT.C4Geo.dpos P m := by
    vsimp [a5, a4, hbv]
  have hq5 : a5.env StageHamming.columnTarget = q := by vsimp [a5, a4, hbq]
  have hsb : b.env StageHamming.parityWidth = P.s := (hbfr _ (by decide)).trans hs3
  have hs5 : a5.env StageHamming.parityWidth = P.s := by vsimp [a5, a4, hsb]
  refine Hs.then (StageHamming.columnBit_cwBit_spec a5 hc5 P (PrimT.C4Geo.dpos P m) q
    hi5 hq5 hs5 (by omega) (by omega) (by omega) (by omega) (by omega))
    (fun d ⟨hdv, hdsh, hdfr⟩ n7 hn7 => ?_)
  refine Hs.last (hs_copy C result StageHamming.columnOutput d (by decide)) ?_
  rintro e rfl n8 hn8
  have hfd : Fr a d codewordScratch := (hfb.trans hf5).trans (hdfr.weaken (by
    intro y hy
    exact List.mem_append_right _ hy))
  exact ⟨⟨by simpa only [DS.set_env_self] using hdv, hdsh.trans hbsh,
    hfd.trans (Fr.set d _ (by decide))⟩, by omega⟩

end NearQuarticWires.StageColumns
