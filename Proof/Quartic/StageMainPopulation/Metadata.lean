import Proof.Quartic.StageMainPopulation.Request

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open StageMainMask StageCert

def loadMetadata : St VV :=
  .seq (StageOutput.readScalars metadataRegisters)
    (.seq (.op (.copy sourceWitnessBase vPOS)) (.op (.zero populationTotal)))

/-- `def:mask`, witness (W2) and `prop:time`, paper/paper.tex: physically read all five binary
fields and retain the actual cursor immediately before the witness frame. -/
theorem loadMetadata_run (C : Ctx) (a : DS VV) (r : PopulationRequest)
    (hc : Cst a) (hcp : a.cp = (callWord r.call).length)
    (hin : C.cw.drop a.cp = metadataWord r ++ frame r.witness)
    (hW : C.cw.length + 4 ≤ C.Wd)
    (hfields : ∀ f ∈ metadataFields r, natBitLength f.2 ≤ C.cw.length) :
    Hs C loadMetadata a (StageOutput.readScalarsCost (metadataFields r) + 4) (fun b =>
      Loaded b r ∧ b.cp = (witnessPrefix r).length ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b) := by
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by have h := Nat.lt_two_pow_self (n := C.Wd); omega
  have hh := StageOutput.readScalars_spec (C := C) (metadataFields r)
    (by intro f hf; simp only [metadataFields, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide)
    (fun f hf => by have h := hfields f hf; omega) hL (frame r.witness) a hc hin
  rw [metadataRegisters_eq] at hh
  unfold loadMetadata
  refine Hs.seq (t2 := 3) hh ?_
  rintro b ⟨hbcp, hbwq, hbout, hbc, hbenv⟩
  have hpoints : ∀ l, b.env (cornerPoint l) = r.corners l := by
    intro l
    rw [hbenv (cornerPoint l) (by dsimp [cornerPoint]; omega)]
    fin_cases l <;> norm_num [StageOutput.fieldEnv, metadataFields, cornerPoint,
      sourceWitnessIndex, Function.update, Fin.ext_iff]
    all_goals rfl
  have hindex : b.env sourceWitnessIndex = r.offset := by
    simpa (config := {decide := true}) [StageOutput.fieldEnv, metadataFields] using
      hbenv sourceWitnessIndex (by decide)
  have hbpos : b.env vPOS = (witnessPrefix r).length := by
    rw [hbc.pos, hbcp, hcp]
    simp only [witnessPrefix, List.length_append]
    rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C sourceWitnessBase vPOS b (by decide)) ?_
  rintro d rfl
  refine (hs_zero C populationTotal _).mono le_rfl ?_
  rintro e rfl
  refine ⟨⟨?_, ?_, ?_, by simp⟩, ?_, hbwq, hbout, ?_⟩
  · intro l
    rw [DS.set_env_ne _ _ (by fin_cases l <;> decide),
      DS.set_env_ne _ _ (by fin_cases l <;> decide)]
    exact hpoints l
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_self, hbpos]
  · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hindex]
  · rw [DS.set_cp, DS.set_cp, hbcp, hcp]
    simp only [witnessPrefix, List.length_append]
    rfl
  · exact (hbc.set _ _ (by decide)).set _ _ (by decide)

end NearQuarticWires.StageMainPopulation
