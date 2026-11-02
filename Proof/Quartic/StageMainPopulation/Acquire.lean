import Proof.Quartic.StageMainPopulation.Header

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageMain StageCert

def acquireProgram : St VV :=
  .seq skipOriginalCall (.seq loadMetadata returnToFirst)

def acquireSteps (r : PopulationRequest) (L : ℕ) : ℕ :=
  3000 * (L + 2) ^ 3 + StageOutput.readScalarsCost (metadataFields r) + 100 * (L + 2) + 20

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: acquire the actual source fields,
record the literal witness-frame address and reread the real first-list
header without any supplied source position or initialized registers. -/
theorem acquireProgram_run (C : Ctx) (a : DS VV) (r : PopulationRequest)
    (hc : Cst a) (hcp : a.cp = 0) (hin : C.cw = r.word)
    (hW : C.cw.length + 4 ≤ C.Wd) :
    Hs C acquireProgram a (acquireSteps r C.cw.length) (fun b =>
      Loaded b r ∧ b.cp = pos1 r.call ∧ b.env firstStart = pos1 r.call ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  have hb := encoding_bounds r
  have hn : r.call.n ≤ C.cw.length := by rw [hin]; exact hb.1
  have hfields : ∀ f ∈ metadataFields r, natBitLength f.2 ≤ C.cw.length := by
    intro f hf; rw [hin]; exact hb.2.2.2 f hf
  have hsource : C.cw.drop a.cp = callWord r.call ++ (metadataWord r ++ frame r.witness) := by
    rw [hcp, List.drop_zero, hin, request_word]
    simp only [witnessPrefix, List.append_assoc]
  unfold acquireProgram
  refine Hx.hs (Hs.then (skipOriginalCall_spec r.call _ a hc hsource hW hn)
    (fun b ⟨hbcp, hbwq, hbout, hbc⟩ n1 hn1 => ?_))
  have hbcp' : b.cp = (callWord r.call).length := by rw [hbcp, hcp, Nat.zero_add]
  have hbin : C.cw.drop b.cp = metadataWord r ++ frame r.witness := by
    rw [hbcp', hin, request_word]
    simp only [witnessPrefix, List.append_assoc, List.drop_left]
  refine Hs.then (loadMetadata_run C b r hbc hbcp' hbin hW hfields)
    (fun c ⟨hl, _, hcwq, hcout, hcc⟩ n2 hn2 => ?_)
  refine Hs.last (returnToFirst_run C c r hcc hl hin hW) ?_
  rintro d ⟨hd, hdcp, hdfirst, hdwq, hdout, hdc⟩ n3 hn3
  exact ⟨⟨hd, hdcp, hdfirst, hdwq.trans (hcwq.trans hbwq),
    hdout.trans (hcout.trans hbout), hdc⟩, by unfold acquireSteps; omega⟩

end NearQuarticWires.StageMainPopulation
