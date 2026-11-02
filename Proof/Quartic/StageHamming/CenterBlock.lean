import Proof.Quartic.StageHamming.CenterMetadata

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def centerLoadScratch : List (Fin VV) :=
  [encoderCode, encoderCounter, columnTarget, encoderBase]

/-- `imp:partition`, paper/paper.tex: a coordinate
inside a half's coded blocks is split into its actual block and bit
indices, then encoded from the selected original scalar code. -/
def centerBlock (source : Fin VV) : St VV MM :=
  .seq (.op (.copy encoderCode source))
    (.seq (.op (.dm centerLocal dataLimit encoderCounter columnTarget))
      (.seq (.op (.mul encoderCounter encoderLimit encoderBase))
        (.seq encoderBlock (.op (.copy centerOutput encoderAccumulator)))))

/-- `imp:partition`, paper/paper.tex: a real local
block coordinate has an original data-code offset within the original
arity, without expanding a center or basis table. -/
theorem center_block_base_le (P : StarParams) (z : ℕ) (hz : z < P.r / 2 * P.b) :
    z / P.b * PrimT.C4Geo.dB P ≤ P.n := by
  have hblock : z / P.b < P.r / 2 := (Nat.div_lt_iff_lt_mul P.b_pos).mpr hz
  have hd := (block_dimensions_le P).2.2
  exact (Nat.mul_le_mul_left _ hd).trans
    ((Nat.mul_le_mul_right P.b hblock.le).trans
      ((Nat.mul_le_mul_right P.b (Nat.div_le_self P.r 2)).trans P.r_mul_b_le))

/-- `imp:partition`, `imp:pullback` and `prop:time`, paper/paper.tex: an actual original block bit is
computed by division, canonical encoding, and final output copying,
with a fixed cubic source clock and the original point width. -/
theorem centerBlock_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code z : ℕ) (source : Fin VV)
    (hsource : encoderCode ≠ source) (hcode : a.env source = code)
    (hlocal : a.env centerLocal = z) (hready : CenterReady a P)
    (hz : z < P.r / 2 * P.b) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C (centerBlock source) a (200 * (P.n + 1) ^ 3 + 16) (fun b =>
      b.env centerOutput =
        (PrimT.C4Geo.encB P (fun m => code.testBit (z / P.b * PrimT.C4Geo.dB P + m))
          (z % P.b)).toNat ∧ b.sh = a.sh ∧ Fr a b centerScratch) := by
  have hsmall := scalar_word_bound P C.Wd hwidth
  have hbN := (block_dimensions_le P).1
  have hbaseN := center_block_base_le P z hz
  have hbaseW : z / P.b * PrimT.C4Geo.dB P < 2 ^ C.Wd := by omega
  unfold centerBlock
  refine Hx.hs (Hs.then (hs_copy C encoderCode source a hsource)
    (fun b hb n1 hn1 => ?_))
  subst hb
  let a1 := a.set encoderCode (a.env source)
  have hf1 : Fr a a1 centerLoadScratch := Fr.set _ _ (by simp [centerLoadScratch])
  refine Hs.then (hs_dm C centerLocal dataLimit encoderCounter columnTarget a1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hf1 _ (by decide), hready.blockSize]; exact P.b_pos)
    (by rw [hf1 _ (by decide), hready.blockSize]; omega))
    (fun b hb n2 hn2 => ?_)
  subst hb
  let a2 := (a1.set encoderCounter (a1.env centerLocal / a1.env dataLimit)).set columnTarget
    (a1.env centerLocal % a1.env dataLimit)
  have hdim : a2.env encoderCounter * a2.env encoderLimit =
      z / P.b * PrimT.C4Geo.dB P := by
    vsimp [a2, a1, hlocal, hready.blockSize, hready.dataDimension]
  refine Hs.then (hs_mul C encoderCounter encoderLimit encoderBase a2
    (by decide) (by decide) (by decide) (by rw [hdim]; exact hbaseW))
    (fun b hb n3 hn3 => ?_)
  subst hb
  let a3 := a2.set encoderBase (a2.env encoderCounter * a2.env encoderLimit)
  have hf3 : Fr a a3 centerLoadScratch :=
    hf1.trans ((Fr.set a1 _ (by decide)).trans
      ((Fr.set (a1.set encoderCounter (a1.env centerLocal / a1.env dataLimit)) _ (by decide)).trans
        (Fr.set a2 _ (by decide))))
  have hc3 : Cst a3 := hc.of_fr hf3 (by decide)
  have hcode3 : a3.env encoderCode = code := by vsimp [a3, a2, a1, hcode]
  have hbase3 : a3.env encoderBase = z / P.b * PrimT.C4Geo.dB P := by
    rw [DS.set_env_self, hdim]
  have htarget3 : a3.env columnTarget = z % P.b := by
    vsimp [a3, a2, a1, hlocal, hready.blockSize]
  refine Hs.then (encoderBlock_arity_spec a3 hc3 P code
    (z / P.b * PrimT.C4Geo.dB P) (z % P.b)
    ((hf3 _ (by decide)).trans hready.dataDimension) hcode3 hbase3
    ((hf3 _ (by decide)).trans hready.blockSize) ((hf3 _ (by decide)).trans hready.parity)
    htarget3 hbaseN (Nat.mod_lt _ P.b_pos) hwidth)
    (fun b hbp n4 hn4 => ?_)
  obtain ⟨hvalue, hbsh, hbfr⟩ := hbp
  refine Hs.last (hs_copy C centerOutput encoderAccumulator b (by decide)) ?_
  rintro d rfl n5 hn5
  exact ⟨⟨by rw [DS.set_env_self, hvalue], hbsh,
    (hf3.weaken (by decide)).trans
      ((hbfr.weaken (by decide)).trans (Fr.set _ _ (by decide)))⟩, by omega⟩

end NearQuarticWires.StageHamming
