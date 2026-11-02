import Proof.Quartic.StageMainPopulation.State
import Proof.Quartic.StageMain.Circuit

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

/-- `def:class` and `def:mask`, paper/paper.tex: replay the complete original first circuit, including its
encoded coefficients and Boolean top, to locate the actual second bank. -/
def replayFirst : St VV := .seq (seekW firstStart)
  (.seq (.op (.zero StageMain.pointSaved)) StageMain.scoreCircuit)

def replaySteps (L : ℕ) : ℕ := 800 * (L + 2)^3 + 5 * L + 20

def replayScratch : List (Fin VV) := [t0, vPOS, vJ, StageMain.pointSaved] ++ StageMain.scoreCircuitScratch

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: the second-bank source address is
physically rediscovered through the original first top, retaining the
population total, witness index and all four original point codes. -/
theorem replayFirst_run (C : Ctx) (a : DS VV) (r : PopulationRequest)
    (hc : Cst a) (hr : Retained a r) (hin : C.cw = r.word)
    (hW : C.cw.length + 4 ≤ C.Wd) :
    Hs C replayFirst a (replaySteps C.cw.length) (fun b =>
      Retained b r ∧ b.cp = pos2 r.call ∧ b.env populationTotal = a.env populationTotal ∧
      b.env sourceWitnessIndex = a.env sourceWitnessIndex ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  have hstart : pos1 r.call ≤ C.cw.length := by
    rw [hin, source_shape]
    simp only [List.length_append, pos1]
    omega
  have hL : C.cw.length < 2 ^ C.Wd := by have h := Nat.lt_two_pow_self (n := C.Wd); omega
  unfold replayFirst
  refine Hx.hs (Hs.then (seekW_spec firstStart (by decide) (by decide) a hc
    (pos1 r.call) hr.first hstart hL)
    (fun b ⟨hbcp, hbwq, hbout, hbc, hbf⟩ n1 hn1 => ?_))
  refine Hs.then (hs_zero C StageMain.pointSaved b) (fun c he n2 hn2 => ?_)
  subst he
  let c := b.set StageMain.pointSaved 0
  have hcc : Cst c := hbc.set _ _ (by decide)
  have hinput : C.cw.drop c.cp = circuitWord r.call.first ++
      (circuitWord r.call.second ++ sourceTail r) := by
    change C.cw.drop b.cp = _
    rw [hbcp, hin]
    exact firstCircuit_input r
  refine Hs.last (StageMain.scoreCircuit_spec r.call.first c hcc _ hinput hW
    (by simp [c])) ?_
  rintro d ⟨_, hdcp, hdwq, hdout, hdc, hdf⟩ n3 hn3
  have hf : FrS a d replayScratch :=
    (hbf.toS.weaken (by decide)).trans
      (((Fr.set (T := [StageMain.pointSaved]) b 0 (by simp)).toS.weaken (by decide)).trans
        (hdf.weaken (by intro y hy; exact List.mem_append_right _ hy)))
  refine ⟨⟨hr.frame hf (by intro l; fin_cases l <;> decide) (by decide) (by decide), ?_,
    hf _ (by decide) (by decide), hf _ (by decide) (by decide),
    hdwq.trans hbwq, hdout.trans hbout, hdc⟩, by unfold replaySteps; omega⟩
  rw [hdcp]
  change b.cp + (circuitWord r.call.first).length = pos2 r.call
  rw [hbcp]
  rfl

end NearQuarticWires.StageMainPopulation
