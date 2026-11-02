import Proof.Quartic.StageHamming.EncoderPrepare

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def encoderBodyScratch : List (Fin VV) := encoderPrepareScratch ++ columnBitScratch
def encoderStepScratch : List (Fin VV) := encoderAccumulator :: encoderBodyScratch

/-- `imp:partition`, paper/paper.tex: one actual
encoder step prepares its source bit and canonical data position,
computes the corresponding column bit, then performs the gated xor. -/
def encoderStep : St VV MM := .seq encoderPrepare (.seq columnBit encoderAccumulate)

/-- `imp:partition` and `prop:time`, paper/paper.tex: one scalar block step realizes the exact original xor
prefix, including lookup, code selection, column and accumulator costs. -/
theorem encoderStep_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code base q k : ℕ) (hk : k < PrimT.C4Geo.dB P)
    (hcounter : a.env encoderCounter = k) (hcode : a.env encoderCode = code)
    (hbase : a.env encoderBase = base) (hb : a.env dataLimit = P.b)
    (hswidth : a.env parityWidth = P.s) (hq : a.env columnTarget = q)
    (hacc : a.env encoderAccumulator = (encoderPrefix P code base q k).toNat)
    (hbW : P.b < 2 ^ C.Wd) (hs : P.s < 2 ^ C.Wd)
    (hW : 2 ^ P.s < 2 ^ C.Wd) (hindexW : base + k < 2 ^ C.Wd)
    (hqW : q + 1 < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) :
    Hs C encoderStep a
      (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) + 5 * (base + k) + 80)
      (fun b => b.env encoderAccumulator = (encoderPrefix P code base q (k + 1)).toNat ∧
        b.sh = a.sh ∧ Fr a b encoderStepScratch) := by
  unfold encoderStep
  refine Hx.hs (Hs.then (encoderPrepare_spec a hc P code base k hcounter hcode hbase
    hb hswidth hbW hs hW hindexW hwidth) (fun b hbp n1 hn1 => ?_))
  obtain ⟨hpos, hselected, hbsh, hbfr⟩ := hbp
  have hfb : Fr a b encoderBodyScratch := hbfr.weaken (by decide)
  have hcb : Cst b := hc.of_fr hfb (by decide)
  have hposW : PrimT.C4Geo.dpos P k + 1 < 2 ^ C.Wd := by
    have hp := (PrimT.C4Geo.dpos_mem P k hk).1
    omega
  refine Hs.then (columnBit_cwBit_spec b hcb P (PrimT.C4Geo.dpos P k) q
    hpos ((hfb _ (by decide)).trans hq) ((hfb _ (by decide)).trans hswidth)
    hposW hqW hs hwidth hW) (fun c hcp n2 hn2 => ?_)
  obtain ⟨hentry, hcsh, hcfr⟩ := hcp
  have hfc : Fr a c encoderBodyScratch := hfb.trans (hcfr.weaken (by decide))
  have hcc : Cst c := hc.of_fr hfc (by decide)
  refine Hs.last (encoderAccumulate_spec c hcc (encoderPrefix P code base q k)
    (code.testBit (base + k)) (PrimT.C4Geo.cwBit P (PrimT.C4Geo.dpos P k) q)
    ((hfc _ (by decide)).trans hacc) ((hcfr _ (by decide)).trans hselected)
    hentry) ?_
  rintro d ⟨hdacc, hdsh, hdfr⟩ n3 hn3
  refine ⟨⟨?_, hdsh.trans (hcsh.trans hbsh),
    (hfc.weaken (by decide)).trans (hdfr.weaken (by decide))⟩, by omega⟩
  rw [encoderPrefix_succ]
  exact hdacc

end NearQuarticWires.StageHamming
