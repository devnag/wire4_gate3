import Proof.Quartic.StageHamming.EncoderAccumulate

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def encoderPrepareScratch : List (Fin VV) :=
  [dataTarget, columnData, encoderSelected, bitInput, bitIndex, bitOutput,
    bitWork, bitCounter, bitQuotient] ++ dataPositionScratch

/-- `imp:partition`, paper/paper.tex: the next block
data position and its selected source bit are physically computed
from the current scalar index and packed code. -/
def encoderPrepare : St VV MM :=
  .seq (.op (.copy dataTarget encoderCounter))
    (.seq dataPosition
      (.seq (.op (.copy columnData dataAnswer))
        (.seq (.op (.copy bitInput encoderCode))
          (.seq (.op (.copy bitIndex encoderBase))
            (.seq (.op (.add bitIndex encoderCounter))
              (.seq readScalarBit (.op (.copy encoderSelected bitOutput))))))))

/-- `imp:partition` and `prop:time`, paper/paper.tex: both the canonical data-position lookup and original
packed-code bit are computed with their complete physical costs. -/
theorem encoderPrepare_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code base k : ℕ)
    (hcounter : a.env encoderCounter = k) (hcode : a.env encoderCode = code)
    (hbase : a.env encoderBase = base) (hb : a.env dataLimit = P.b)
    (hswidth : a.env parityWidth = P.s)
    (hbW : P.b < 2 ^ C.Wd) (hs : P.s < 2 ^ C.Wd)
    (hW : 2 ^ P.s < 2 ^ C.Wd) (hindexW : base + k < 2 ^ C.Wd)
    (hwidth : 2 ≤ C.Wd) :
    Hs C encoderPrepare a (P.b * (8 * P.s + 24) + 5 * (base + k) + 40) (fun b =>
      b.env columnData = PrimT.C4Geo.dpos P k ∧
      b.env encoderSelected = (code.testBit (base + k)).toNat ∧
      b.sh = a.sh ∧ Fr a b encoderPrepareScratch) := by
  unfold encoderPrepare
  refine Hx.hs (Hs.then (hs_copy C dataTarget encoderCounter a (by decide))
    (fun b hb' n1 hn1 => ?_))
  subst hb'
  let a1 := a.set dataTarget (a.env encoderCounter)
  have hf1 : Fr a a1 encoderPrepareScratch := Fr.set _ _ (by decide)
  have hc1 : Cst a1 := hc.of_fr hf1 (by decide)
  refine Hs.then (dataPosition_dpos_spec a1 hc1 P k
    ((hf1 _ (by decide)).trans hb) ((hf1 _ (by decide)).trans hswidth)
    (by rw [DS.set_env_self, hcounter]) hbW hs hW)
    (fun b hbp n2 hn2 => ?_)
  obtain ⟨hpos, hbsh, hbfr⟩ := hbp
  have hfb : Fr a b encoderPrepareScratch := hf1.trans (hbfr.weaken (by decide))
  have hbcode : b.env encoderCode = code := (hfb _ (by decide)).trans hcode
  have hbbase : b.env encoderBase = base := (hfb _ (by decide)).trans hbase
  have hbcounter : b.env encoderCounter = k := (hfb _ (by decide)).trans hcounter
  refine Hs.then (hs_copy C columnData dataAnswer b (by decide))
    (fun c hc' n3 hn3 => ?_)
  subst hc'
  let a3 := b.set columnData (b.env dataAnswer)
  refine Hs.then (hs_copy C bitInput encoderCode a3 (by decide))
    (fun c hc' n4 hn4 => ?_)
  subst hc'
  let a4 := a3.set bitInput (a3.env encoderCode)
  refine Hs.then (hs_copy C bitIndex encoderBase a4 (by decide))
    (fun c hc' n5 hn5 => ?_)
  subst hc'
  let a5 := a4.set bitIndex (a4.env encoderBase)
  have ha5index : a5.env bitIndex + a5.env encoderCounter = base + k := by
    vsimp [a5, a4, a3, hbbase, hbcounter]
  refine Hs.then (hs_add C bitIndex encoderCounter a5 (by decide)
    (by rw [ha5index]; exact hindexW)) (fun c hc' n6 hn6 => ?_)
  subst hc'
  let a6 := a5.set bitIndex (a5.env bitIndex + a5.env encoderCounter)
  have hf6 : Fr a a6 encoderPrepareScratch :=
    hfb.trans ((Fr.set b _ (by decide)).trans ((Fr.set a3 _ (by decide)).trans
      ((Fr.set a4 _ (by decide)).trans (Fr.set a5 _ (by decide)))))
  have hc6 : Cst a6 := hc.of_fr hf6 (by decide)
  have ha6index : a6.env bitIndex = base + k := by rw [DS.set_env_self, ha5index]
  have ha6code : a6.env bitInput = code := by vsimp [a6, a5, a4, a3, hbcode]
  have ha6pos : a6.env columnData = PrimT.C4Geo.dpos P k := by
    vsimp [a6, a5, a4, a3, hpos]
  refine Hs.then (readScalarBit_spec a6 hc6 (by rw [ha6index]; exact hindexW) hwidth)
    (fun c hcp n7 hn7 => ?_)
  obtain ⟨hbit, hcsh, hcfr⟩ := hcp
  have hselected : c.env bitOutput = (code.testBit (base + k)).toNat := by
    simpa only [ha6code, ha6index] using hbit
  refine Hs.last (hs_copy C encoderSelected bitOutput c (by decide)) ?_
  rintro d rfl n8 hn8
  refine ⟨⟨?_, ?_, hcsh.trans hbsh,
    hf6.trans ((hcfr.weaken (by decide)).trans (Fr.set _ _ (by decide)))⟩, ?_⟩
  · rw [DS.set_env_ne _ _ (by decide)]
    exact (hcfr _ (by decide)).trans ha6pos
  · rw [DS.set_env_self, hselected]
  · rw [ha6index] at hn7
    omega

end NearQuarticWires.StageHamming
