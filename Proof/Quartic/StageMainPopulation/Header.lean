import Proof.Quartic.StageMainPopulation.Metadata

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageMain StageCert

def returnToFirst : St VV :=
  .seq (seekW vZ) (.seq callHeader (.op (.copy firstStart vPOS)))

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: physically rewind and reread the
actual original call header while retaining all population source fields. -/
theorem returnToFirst_run (C : Ctx) (a : DS VV) (r : PopulationRequest)
    (hc : Cst a) (hl : Loaded a r) (hin : C.cw = r.word)
    (hW : C.cw.length + 4 ≤ C.Wd) :
    Hs C returnToFirst a (100 * (C.cw.length + 2)) (fun b =>
      Loaded b r ∧ b.cp = pos1 r.call ∧ b.env firstStart = pos1 r.call ∧
      b.wq = a.wq ∧ b.out = a.out ∧ Cst b) := by
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by have h := Nat.lt_two_pow_self (n := C.Wd); omega
  have hn := natBitLength_le_len r.call.n
  have ht := natBitLength_le_len (kindTag r.call.kind)
  have hlen : (natWord r.call.n).length + (natWord (kindTag r.call.kind)).length ≤ C.cw.length := by
    rw [hin]
    simp only [PopulationRequest.word, callWord, List.length_append]
    omega
  unfold returnToFirst
  refine Hx.hs (Hs.then (seekW_spec vZ (by decide) (by decide) a hc 0 hc.z
    (by omega) (by omega)) (fun b ⟨hbcp, hbwq, hbout, hbc, hbf⟩ n1 hn1 => ?_))
  have hinput : C.cw.drop b.cp = natWord r.call.n ++
      (natWord (kindTag r.call.kind) ++
        (circuitWord r.call.first ++ circuitWord r.call.second ++
          listWord natWord r.call.parity ++ ratWord r.call.radius ++
            natWord r.offset ++ (List.ofFn r.corners).flatMap natWord ++ frame r.witness)) := by
    rw [hbcp, List.drop_zero, hin]
    simp only [PopulationRequest.word, callWord, List.append_assoc]
  refine Hs.then (callHeader_spec b hbc r.call.n (kindTag r.call.kind) _ hinput
    (by omega) (by omega) hL) (fun c ⟨_, _, hccp, hcwq, hcout, hcc, hcf⟩ n2 hn2 => ?_)
  have hcp : c.cp = pos1 r.call := by rw [hccp, hbcp, Nat.zero_add]; rfl
  have hf : Fr a c ([t0, vPOS, vJ] ++ callHeaderScratch) :=
    (hbf.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans
      (hcf.weaken (by intro y hy; exact List.mem_append_right _ hy))
  refine Hs.last (hs_copy C firstStart vPOS c (by decide)) ?_
  rintro d rfl n3 hn3
  refine ⟨⟨?_, hcp, by rw [DS.set_env_self, hcc.pos, hcp],
    hcwq.trans hbwq, hcout.trans hbout, hcc.set _ _ (by decide)⟩, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l
    rw [DS.set_env_ne _ _ (by fin_cases l <;> decide), hf _ (by fin_cases l <;> decide)]
    exact hl.corners l
  · rw [DS.set_env_ne _ _ (by decide), hf _ (by decide), hl.witnessBase]
  · rw [DS.set_env_ne _ _ (by decide), hf _ (by decide), hl.index]
  · rw [DS.set_env_ne _ _ (by decide), hf _ (by decide), hl.total]

end NearQuarticWires.StageMainPopulation
