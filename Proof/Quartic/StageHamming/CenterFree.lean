import Proof.Quartic.StageHamming.CenterBlock

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def centerFreeScratch : List (Fin VV) :=
  [bitInput, encoderBase, bitIndex, bitOutput, bitWork, bitCounter, bitQuotient, centerOutput]

/-- `imp:partition` and `imp:pullback`, paper/paper.tex: a free-tail coordinate is read from its actual
original scalar code after the coded-block data offset. -/
def centerFreeBit (source : Fin VV) : St VV MM :=
  .seq (.op (.copy bitInput source))
    (.seq (.op (.mul centerHalf encoderLimit encoderBase))
      (.seq (.op (.copy bitIndex centerLocal))
        (.seq (.op (.add bitIndex encoderBase))
          (.seq readScalarBit (.op (.copy centerOutput bitOutput))))))

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: the actual free-coordinate
reader computes the literal scalar bit with a linear native clock,
preserving the original metadata and every other point component. -/
theorem centerFreeBit_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code z : ℕ) (source : Fin VV)
    (hsource : bitInput ≠ source) (hcode : a.env source = code)
    (hlocal : a.env centerLocal = z) (hready : CenterReady a P)
    (hz : z ≤ P.n) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C (centerFreeBit source) a (10 * P.n + 32) (fun b =>
      b.env centerOutput = (code.testBit (P.r / 2 * PrimT.C4Geo.dB P + z)).toNat ∧
      b.sh = a.sh ∧ Fr a b centerScratch) := by
  have hsmall := scalar_word_bound P C.Wd hwidth
  have hd := (block_dimensions_le P).2.2
  have hbaseN : P.r / 2 * PrimT.C4Geo.dB P ≤ P.n :=
    (Nat.mul_le_mul_left _ hd).trans
      ((Nat.mul_le_mul_right P.b (Nat.div_le_self P.r 2)).trans P.r_mul_b_le)
  have hbaseW : P.r / 2 * PrimT.C4Geo.dB P < 2 ^ C.Wd := by omega
  have hindexW : P.r / 2 * PrimT.C4Geo.dB P + z < 2 ^ C.Wd := by omega
  unfold centerFreeBit
  refine Hx.hs (Hs.then (hs_copy C bitInput source a hsource)
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set bitInput (a.env source)
  refine Hs.then (hs_mul C centerHalf encoderLimit encoderBase a1
    (by decide) (by decide) (by decide)
    (by simpa (config := { decide := true })
      [a1, DS.set, hready.half, hready.dataDimension] using hbaseW))
    (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := a1.set encoderBase (a1.env centerHalf * a1.env encoderLimit)
  refine Hs.then (hs_copy C bitIndex centerLocal a2 (by decide))
    (fun b hb n3 hn3 => ?_)
  subst hb
  let a3 := a2.set bitIndex (a2.env centerLocal)
  have hindex : a3.env bitIndex + a3.env encoderBase =
      P.r / 2 * PrimT.C4Geo.dB P + z := by
    vsimp [a3, a2, a1, hready.half, hready.dataDimension, hlocal, Nat.add_comm]
  refine Hs.then (hs_add C bitIndex encoderBase a3 (by decide)
    (by rw [hindex]; exact hindexW)) (fun b hb n4 hn4 => ?_)
  subst hb
  let a4 := a3.set bitIndex (a3.env bitIndex + a3.env encoderBase)
  have hf4 : Fr a a4 centerFreeScratch :=
    (Fr.set a _ (by decide)).trans ((Fr.set a1 _ (by decide)).trans
      ((Fr.set a2 _ (by decide)).trans (Fr.set a3 _ (by decide))))
  have hc4 : Cst a4 := hc.of_fr hf4 (by decide)
  have hi4 : a4.env bitIndex = P.r / 2 * PrimT.C4Geo.dB P + z := by
    rw [DS.set_env_self, hindex]
  have hcode4 : a4.env bitInput = code := by vsimp [a4, a3, a2, a1, hcode]
  refine Hs.then (readScalarBit_spec a4 hc4 (by rw [hi4]; exact hindexW) (by omega))
    (fun b hbp n5 hn5 => ?_)
  obtain ⟨hbit, hbsh, hbfr⟩ := hbp
  refine Hs.last (hs_copy C centerOutput bitOutput b (by decide)) ?_
  rintro d rfl n6 hn6
  refine ⟨⟨?_, hbsh, (hf4.weaken (by decide)).trans
    ((hbfr.weaken (by decide)).trans (Fr.set _ _ (by decide)))⟩, ?_⟩
  · rw [DS.set_env_self, hbit, hcode4, hi4]
  · rw [hi4] at hn5
    omega

end NearQuarticWires.StageHamming
