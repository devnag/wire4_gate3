import Proof.Quartic.StageRecovery.FamilyInputReady
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the finite cache
input program initializes its own constants and reads the original
Formula metadata before loading the appended generated family. -/
def coldFamilyCacheProgram : St VV MM :=
  .seq initP (.seq familyHeaderProgram prepareFamilyCacheProgram)

/-- `prop:time`, paper/paper.tex: the cold cache input
clock includes initialization, every actual header byte, packet parsing,
the complete input return and the physical generated-record rewind. -/
def FamilyCompileRequest.coldCacheSteps (r : FamilyCompileRequest) : ℕ :=
  5 + (StageGamma.readFieldsCost r.header + r.prepareCacheSteps + 1) + 1

/-- `lem:print`, paper/paper.tex: the literal retained
source followed by the native packet reaches the actual empty-cache
state from the initialized multitape machine, with no supplied records. -/
theorem coldFamilyCacheProgram_spec (C : Ctx) (r : FamilyCompileRequest)
    (hin : C.inp = r.word ++ r.family.output)
    (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd) :
    Hs C coldFamilyCacheProgram (a0 : DS VV MM) r.coldCacheSteps
      (FamilyCacheReady r (r.header.flatMap natWord).length) := by
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hfields : ∀ v ∈ r.header, natBitLength v + 2 ≤ C.Wd := by
    intro v hv
    have h := r.header_bits v hv
    omega
  unfold coldFamilyCacheProgram FamilyCompileRequest.coldCacheSteps
  refine Hs.seq (t2 := StageGamma.readFieldsCost r.header + r.prepareCacheSteps + 1)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    fun a ⟨hc, hram, hrc, hip, hout, _, _, _, _⟩ => ?_
  change a.ram = fun _ => [] at hram
  change a.rc = fun _ => 0 at hrc
  change a.ip = 0 at hip
  change a.out = [] at hout
  refine Hs.seq (t2 := r.prepareCacheSteps)
    (familyHeaderProgram_suffix_spec C a hc r r.family.output
      (by rw [hip]; simpa only [List.drop_zero] using hin) hfields)
    fun b ⟨hbD, hbV, _, _, hbq, hbN, hbL, hbi, hbr, hbc, _⟩ => ?_
  have hbram : b.ram = a.ram := congrArg (fun x => x.2.1) hbr
  have hbrc : b.rc = a.rc := congrArg (fun x => x.2.2.1) hbr
  have hbout : b.out = a.out := congrArg Prod.fst hbr
  have hsource : C.inp.drop b.ip = tokenStream (toks r.source.formula) ++ r.family.output := by
    rw [hbi, hip, zero_add, hin, r.word_eq_header]
    simp only [List.append_assoc, List.drop_left]
  refine (prepareFamilyCacheProgram_spec C b hbc r hwidth hbV hbD hbq hbN hbL hsource
    (hbram.trans hram) (hbrc.trans hrc) (hbout.trans hout)).mono le_rfl ?_
  intro d hd
  have hpos : b.ip = (r.header.flatMap natWord).length := by
    omega
  simpa only [hpos] using hd

end NearQuarticWires.StageRecovery
