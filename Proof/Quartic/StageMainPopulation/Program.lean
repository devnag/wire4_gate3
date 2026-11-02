import Proof.Quartic.StageMainPopulation.Acquire
import Proof.Quartic.StageMainPopulation.FirstBank
import Proof.Quartic.StageMainPopulation.Replay
import Proof.Quartic.StageMainPopulation.SecondBank
import Proof.Quartic.StageMainPopulation.Output

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

def bankSteps (count L : ℕ) : ℕ := count * (900 * (L + 2)^2 + 106) + 30 * natBitLength count + 37

def rawSteps (r : PopulationRequest) (L : ℕ) : ℕ :=
  acquireSteps r L + bankSteps r.call.first.gates.length L + replaySteps L +
    bankSteps r.call.second.gates.length L + 40 * natBitLength r.value + 100

/-- `def:mask` and witness (W2), paper/paper.tex: initialize from the cold state, acquire literal source
metadata, scan both original banks with their real witness positions,
traverse the first top and print the exact binary population value. -/
def rawProgram : St VV :=
  .seq StageOutput.constants (.seq acquireProgram (.seq populationList
    (.seq replayFirst (.seq populationList emitPopulation))))

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: the literal original call, five
binary fields and framed witness compute exactly the requested two-bank
population from the genuine cold state with every source step paid. -/
theorem rawProgram_run (C : Ctx) (r : PopulationRequest)
    (hin : C.cw = r.word) (hW : 2 * C.cw.length + 8 ≤ C.Wd) :
    Hs C rawProgram a0 (rawSteps r C.cw.length) (fun b => b.out = natWord r.value) := by
  have hcount := counts_le r
  rw [← hin] at hcount
  have hvalue := value_le r
  have hsmall := Nat.lt_two_pow_self (n := C.Wd)
  have hbits : natBitLength r.value ≤ 2 * C.cw.length + 1 := by
    have h := Nat.log_le_self 2 r.value
    unfold natBitLength
    omega
  unfold rawProgram
  refine Hx.hs (Hs.then (StageOutput.constants_spec (C := C) (by omega))
    (fun a ⟨hc, hcp, _, hout⟩ n1 hn1 => ?_))
  refine Hs.then (acquireProgram_run C a r hc hcp hin (by omega))
    (fun b ⟨hl, hbcp, hbfirst, _, hbout, hbc⟩ n2 hn2 => ?_)
  have hr : Retained b r := ⟨hl.corners, hl.witnessBase, hbfirst⟩
  refine Hs.then (firstBank_run C b r hbc hr hbcp hl.index hl.total hin hW)
    (fun c ⟨hcr, hctotal, hcindex, _, hcout, hcc⟩ n3 hn3 => ?_)
  refine Hs.then (replayFirst_run C c r hcc hcr hin (by omega))
    (fun d ⟨hdr, hdcp, hdtotal, hdindex, _, hdout, hdc⟩ n4 hn4 => ?_)
  refine Hs.then (secondBank_run C d r hdc hdr hdcp (hdindex.trans hcindex)
    (hdtotal.trans hctotal) hin hW)
    (fun e ⟨hetotal, _, heout, hec⟩ n5 hn5 => ?_)
  refine Hs.last (emitPopulation_run C e hec r.value hetotal (by omega) (by omega)) ?_
  rintro f hfout n6 hn6
  refine ⟨?_, ?_⟩
  · rw [hfout, heout, hdout, hcout, hbout, hout, List.nil_append]
  · unfold rawSteps bankSteps
    omega

end NearQuarticWires.StageMainPopulation
