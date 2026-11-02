import Proof.Quartic.StageHamming.EncoderStep

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

def encoderLoopScratch : List (Fin VV) := encoderCounter :: encoderStepScratch

/-- `imp:partition`, paper/paper.tex: the actual
block encoder scans its full original data dimension once. -/
def encoderLoop : St VV MM := forS encoderCounter encoderLimit encoderStep

/-- `imp:partition` and `prop:time`, paper/paper.tex: the paid data-coordinate loop realizes the exact
canonical xor prefix and preserves the retained original code. -/
theorem encoderLoop_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code base q : ℕ)
    (hlimit : a.env encoderLimit = PrimT.C4Geo.dB P)
    (hcode : a.env encoderCode = code) (hbase : a.env encoderBase = base)
    (hb : a.env dataLimit = P.b) (hswidth : a.env parityWidth = P.s)
    (hq : a.env columnTarget = q) (hacc : a.env encoderAccumulator = 0)
    (hbW : P.b < 2 ^ C.Wd) (hs : P.s < 2 ^ C.Wd)
    (hW : 2 ^ P.s < 2 ^ C.Wd) (hregion : base + PrimT.C4Geo.dB P < 2 ^ C.Wd)
    (hqW : q + 1 < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) :
    Hs C encoderLoop a
      (PrimT.C4Geo.dB P * (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) +
        5 * (base + PrimT.C4Geo.dB P) + 84) + 4)
      (fun b => b.env encoderAccumulator =
          (encoderPrefix P code base q (PrimT.C4Geo.dB P)).toNat ∧
        b.sh = a.sh ∧ Fr a b encoderLoopScratch) := by
  let Inv : ℕ → DS VV MM → Prop := fun k b =>
    b.env encoderAccumulator = (encoderPrefix P code base q k).toNat ∧
      b.env encoderCode = code ∧ b.env encoderBase = base ∧ b.env dataLimit = P.b ∧
      b.env parityWidth = P.s ∧ b.env columnTarget = q ∧ b.sh = a.sh ∧
      Fr a b encoderLoopScratch
  have hN : PrimT.C4Geo.dB P < 2 ^ C.Wd := by
    have : PrimT.C4Geo.dB P ≤ P.b := Nat.sub_le _ _
    omega
  have hloop := forS_spec' (C := C) encoderCounter encoderLimit (by decide)
    encoderStep a (PrimT.C4Geo.dB P) hN Inv
    (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) +
      5 * (base + PrimT.C4Geo.dB P) + 80)
    (fun k b v hb' => by
      obtain ⟨ha, hco, hba, hbl, hsw, hqt, hsh, hfr⟩ := hb'
      exact ⟨(DS.set_env_ne _ _ (by decide)).trans ha,
        (DS.set_env_ne _ _ (by decide)).trans hco,
        (DS.set_env_ne _ _ (by decide)).trans hba,
        (DS.set_env_ne _ _ (by decide)).trans hbl,
        (DS.set_env_ne _ _ (by decide)).trans hsw,
        (DS.set_env_ne _ _ (by decide)).trans hqt,
        hsh, hfr.trans (Fr.set _ _ (by decide))⟩)
    (by exact ⟨by simpa [encoderPrefix, PrimT.C4Geo.xr] using hacc,
      hcode, hbase, hb, hswidth, hq, rfl, Fr.refl _ _⟩) hlimit ?_
  · refine hloop.mono (by apply le_of_eq; ring) ?_
    rintro b ⟨⟨ha, _, _, _, _, _, hsh, hfr⟩, _, _⟩
    exact ⟨ha, hsh, hfr⟩
  · intro k hk b hb' hcounter hlim
    obtain ⟨ha, hco, hba, hbl, hsw, hqt, hsh, hfr⟩ := hb'
    have hcb : Cst b := hc.of_fr hfr (by decide)
    refine (encoderStep_spec b hcb P code base q k hk hcounter hco hba hbl hsw hqt
      ha hbW hs hW (by omega) hqW hwidth).mono (by omega) ?_
    rintro d ⟨da, dsh, dfr⟩
    exact ⟨⟨da, (dfr _ (by decide)).trans hco, (dfr _ (by decide)).trans hba,
      (dfr _ (by decide)).trans hbl, (dfr _ (by decide)).trans hsw,
      (dfr _ (by decide)).trans hqt, dsh.trans hsh,
      hfr.trans (dfr.weaken (by decide))⟩,
      (dfr _ (by decide)).trans hcounter, (dfr _ (by decide)).trans hlim⟩

/-- `imp:partition`, paper/paper.tex: the complete
canonical block encoder initializes its actual xor accumulator. -/
def encoderBlock : St VV MM := .seq (.op (.zero encoderAccumulator)) encoderLoop

/-- `imp:partition` and `prop:time`, paper/paper.tex: the complete physical block program returns the exact
original `encB`, paying all lookup, selection, column, and xor loops. -/
theorem encoderBlock_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code base q : ℕ)
    (hlimit : a.env encoderLimit = PrimT.C4Geo.dB P)
    (hcode : a.env encoderCode = code) (hbase : a.env encoderBase = base)
    (hb : a.env dataLimit = P.b) (hswidth : a.env parityWidth = P.s)
    (hq : a.env columnTarget = q)
    (hbW : P.b < 2 ^ C.Wd) (hs : P.s < 2 ^ C.Wd)
    (hW : 2 ^ P.s < 2 ^ C.Wd) (hregion : base + PrimT.C4Geo.dB P < 2 ^ C.Wd)
    (hqW : q + 1 < 2 ^ C.Wd) (hwidth : 2 ≤ C.Wd) :
    Hs C encoderBlock a
      (PrimT.C4Geo.dB P * (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) +
        5 * (base + PrimT.C4Geo.dB P) + 84) + 6)
      (fun b => b.env encoderAccumulator =
          (PrimT.C4Geo.encB P (fun m => code.testBit (base + m)) q).toNat ∧
        b.sh = a.sh ∧ Fr a b encoderLoopScratch) := by
  unfold encoderBlock
  refine Hx.hs (Hs.then (hs_zero C encoderAccumulator a) (fun b hb' n1 hn1 => ?_))
  subst hb'
  let a1 := a.set encoderAccumulator 0
  have hf : Fr a a1 encoderLoopScratch := Fr.set _ _ (by decide)
  have hc1 : Cst a1 := hc.of_fr hf (by decide)
  refine Hs.last (encoderLoop_spec a1 hc1 P code base q
    ((hf _ (by decide)).trans hlimit) ((hf _ (by decide)).trans hcode)
    ((hf _ (by decide)).trans hbase) ((hf _ (by decide)).trans hb)
    ((hf _ (by decide)).trans hswidth) ((hf _ (by decide)).trans hq)
    (by rw [DS.set_env_self]) hbW hs hW hregion hqW hwidth) ?_
  rintro b ⟨ha, hsh, hfr⟩ n2 hn2
  exact ⟨⟨ha, hsh, hf.trans hfr⟩, by omega⟩

end NearQuarticWires.StageHamming
