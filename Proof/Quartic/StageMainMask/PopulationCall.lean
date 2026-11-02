import Proof.Quartic.StageMainMask.StructuralCall
import Proof.Quartic.StageMainMask.PopulationWriter

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual original population request is emitted, run through its
cold ordinary machine and decoded completely from its framed answer. -/
def populationStep : St VV MM :=
  .seq emitPopulationInput (.seq (.op .kcall) readPopulationReply)

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
the actual two-bank original source returns its exact integer
population while preserving all original request records and corners. -/
theorem populationStep_run {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B : ℕ) (a : DS VV MM)
    (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hcur : ∀ store, a.rc store ≤ (a.ram store).length)
    (hempty : a.ram populationReplyStore = [])
    (hW : 2 ≤ width) (hcall : (callWord r.call).length < 2 ^ width)
    (hwit : (Program.witnessPrefix r.call r.selected.1 r.witness).length < 2 ^ width)
    (hfit : ∀ p ∈ populationInputFields r, natBitLength p.2 + 2 < 2 ^ width)
    (hvalue : natBitLength (entryPopulationRequest r).value + 2 ≤ width)
    (hL : 2 + (entryPopulationRequest r).word.length ≤ L)
    (hB : (entryCallee B1 B2).bud (.inr (.inl (entryPopulationRequest r))) ≤ B) :
    Hs (entryContext B1 B2 width input L B) populationStep a
      (a.rc callStore + a.rc witnessStore + 8 * (callWord r.call).length +
        10 * (Program.witnessPrefix r.call r.selected.1 r.witness).length +
        naturalFieldsCost (populationInputFields r) +
        9 * (natWord (entryPopulationRequest r).value).length +
        30 * natBitLength (entryPopulationRequest r).value + L + B + 80)
      (fun b => b.env populationValue = (entryPopulationRequest r).value ∧
        b.env structuralFlag = a.env structuralFlag ∧ b.kin = [] ∧
        b.kout = (entryPopulationRequest r).output ∧
        b.kc = (entryPopulationRequest r).output.length ∧ b.ip = a.ip ∧ b.out = a.out ∧
        (∀ other, other ≠ populationReplyStore → b.ram other = a.ram other) ∧
        Cst b ∧ EntryNumericData r b ∧ Fr a b entryEvaluationScratch) := by
  let C := entryContext B1 B2 width input L B
  obtain ⟨b, nw, hew, hnw, hbkin, hbi, hbo, hbm, _hbko, _hbkc, hbc, hbfr, _hbdata⟩ :=
    emitPopulationInput_run C r a hc ha hkin hW hcall hwit hfit hL
  have hbcur := hew.rc_le hcur
  have hbempty : b.ram populationReplyStore = [] := (congrFun hbm _).trans hempty
  have hbcursor : b.rc populationReplyStore = 0 := by
    have h := hbcur populationReplyStore
    rw [hbempty, List.length_nil] at h
    omega
  have hin : b.kin = C.K.inw (.inr (.inl (entryPopulationRequest r))) := hbkin
  obtain ⟨d, nc, hec, hnc, hdeq⟩ :=
    (Hs.op (OpEx.kcall (C := C) (.inr (.inl (entryPopulationRequest r))) b hin hB) rfl :
      Hs C (.op .kcall) b (1 + L + B)
        (fun d => d = b.called (entryPopulationRequest r).output))
  subst d
  let d := b.called (entryPopulationRequest r).output
  have hdc : Cst d := ⟨hbc.z, hbc.one, hbc.two⟩
  obtain ⟨g, nr, her, hnr, hgv, hgkc, hgi, hgo, hgkin, hgkout, hgm, hgc, hgfr⟩ :=
    readPopulationReply_run C (entryPopulationRequest r).value d hdc rfl rfl hbempty hbcursor hvalue
  have hgf : Fr a g entryEvaluationScratch :=
    (hbfr.weaken (by
      intro x hx
      simp only [entryEvaluationScratch, List.mem_append]
      exact Or.inl (Or.inl hx))).trans (hgfr.weaken (by
        intro x hx
        simp only [entryEvaluationScratch, List.mem_append]
        exact Or.inl (Or.inr hx)))
  have hgrm : ∀ other, other ≠ populationReplyStore → g.ram other = a.ram other := by
    intro other hother
    exact (hgm other hother).trans (congrFun hbm other)
  unfold populationStep
  refine ⟨g, nw + (nc + nr + 1) + 1, Ex.seq hew (Ex.seq hec her), by omega,
    hgv, ?_, hgkin, hgkout, hgkc, hgi.trans hbi, hgo.trans hbo, hgrm,
    hgc, ha.of_evaluation (hgrm _ (by decide)) (hgrm _ (by decide)) (hgrm _ (by decide)) hgf, hgf⟩
  exact (hgfr structuralFlag (by decide)).trans (hbfr structuralFlag (by decide))

end NearQuarticWires.StageMainMask
