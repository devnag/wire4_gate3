import Proof.Quartic.StageMainPopulation.SourceWords

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

def emitPopulation : St VV := .seq (.op (.copy t3 populationTotal)) emitNat

/-- `def:mask` and `prop:time`, paper/paper.tex: print the actual exact population accumulator in binary,
including zero, with every physical natural-codec operation charged. -/
theorem emitPopulation_run (C : Ctx) (a : DS VV) (hc : Cst a) (v : ℕ)
    (hv : a.env populationTotal = v) (hW : 2 ≤ C.Wd)
    (hfit : natBitLength v + 2 < 2 ^ C.Wd) :
    Hs C emitPopulation a (40 * natBitLength v + 42) (fun b =>
      b.out = a.out ++ natWord v) := by
  unfold emitPopulation
  refine (Hs.seq (t1 := 1) (t2 := 40 * natBitLength v + 40)
    (hs_copy C t3 populationTotal a (by decide)) ?_).mono (by omega) (fun _ h => h)
  rintro b rfl
  have hbc : Cst (a.set t3 (a.env populationTotal)) := hc.set _ _ (by decide)
  have hem := emitNat_spec (C := C) _ hbc hW (by rw [DS.set_env_self, hv]; exact hfit)
  rw [DS.set_env_self, hv] at hem
  simpa only [hv, DS.set_out] using
    hem.mono le_rfl (by rintro b ⟨ho, _, _, _, _⟩; exact ho)

end NearQuarticWires.StageMainPopulation
