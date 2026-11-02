import Proof.Quartic.StageMainMask.StructuralSizes
import Proof.Quartic.StageMainMask.StructuralMachine
import Proof.Quartic.StageGamma.FieldProducer
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain

/-- `def:mask` and `prop:time`, paper/paper.tex: one cold program initializes its constants, acquires the
actual finite source and prints the exact framed scan request. -/
def structuralFormatterProgram : St VV MM :=
  .seq initP (framedOutputProgram structuralFormatterRaw)

/-- `def:mask` and `prop:time`, paper/paper.tex: the exact prepared source is formatted from the cold state,
with all initialization, markers and source reads included. -/
theorem structuralFormatterProgram_run {B1 B2 : ℕ} (C : Ctx) (r : StructuralRequest B1 B2)
    (hin : C.inp = structuralWord r)
    (hwidth : (structuralWord r).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd) :
    Hs C structuralFormatterProgram (a0 : DS VV MM)
      (3 * structuralFormatterSteps r + 8) (fun b =>
        b.out = frame (structuralRawRequest r).word) := by
  unfold structuralFormatterProgram
  refine (Hs.seq (t2 := 3 * structuralFormatterSteps r + 2)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl
      (lt_trans (by omega) Nat.lt_two_pow_self)) ?_).mono (by omega) (fun _ h => h)
  rintro a ⟨hc, hram, hrc, hip, hout, _hkin, _hkout, _hkc, _hfr⟩
  change a.ip = 0 at hip
  change a.out = [] at hout
  obtain ⟨b, n, he, hn, ho⟩ := structuralFormatterRaw_run C r [] a hc
    (by simp only [hip, List.drop_zero, hin, List.append_nil]) hwidth h64
    (by intro store; rw [hram, hrc]; exact ⟨rfl, rfl⟩)
  have hm : markOutputState a = a := by
    unfold markOutputState
    simp only [hout, List.flatMap_nil]
    rw [← hout]
  have hf := framedOutput_run he
  rw [hm] at hf
  refine ⟨{ b with out := frame b.out }, 3 * n + 2, hf, by omega, ?_⟩
  change frame b.out = _
  rw [ho, hout, List.nil_append]

/-- `prop:time`, paper/paper.tex: the formatter's
ordinary bit clock includes the full compiler and head restoration. -/
noncomputable def structuralFormatterBudget {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : ℕ :=
  langBudget StageGamma.fieldProducerCallee (structuralSizes B1 B2) VV MM
    (structuralWord r) (3 * structuralFormatterSteps r + 8)

/-- `def:mask` and `prop:time`, paper/paper.tex: an actual cold ordinary machine produces the structural
scan request from the original prep word and two binary indices. -/
noncomputable def structuralFormatterMachine (B1 B2 : ℕ) :
    WordFunction (StructuralRequest B1 B2) structuralWord
      (fun r => frame (structuralRawRequest r).word) structuralFormatterBudget :=
  wordFunction_of_lang structuralWord (fun r => frame (structuralRawRequest r).word)
    StageGamma.fieldProducerCallee (structuralSizes B1 B2) structuralFormatterProgram
    (fun r => 3 * structuralFormatterSteps r + 8) (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := structuralFormatterProgram_run
        (ctxOf StageGamma.fieldProducerCallee (structuralSizes B1 B2) (structuralWord r)) r
        rfl (structuralSizes_width r) (structuralSizes_min B1 B2 _)
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      exact le_trans (by decide) (structuralSizes_min B1 B2 _))

/-- `prop:time`, paper/paper.tex: the shared
structural clock charges source acquisition and the complete exact
mask scan, including the physical stream handoff. -/
noncomputable def structuralBudget {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : ℕ :=
  4 * structuralFormatterBudget r + 4 * structuralRawBudget (structuralRawRequest r) + 12

/-- `def:mask`, Step 4 of `sec:algorithm`, and `prop:time`,
paper/paper.tex: the one
shared cold structural machine returns the actual framed Boolean mask
from the literal prep source and actual pattern indices. -/
noncomputable def structuralWordFunction (B1 B2 : ℕ) :
    WordFunction (StructuralRequest B1 B2) structuralWord structuralOutput structuralBudget := by
  let g : WordFunction (StructuralRequest B1 B2) (fun r => (structuralRawRequest r).word)
      structuralOutput (fun r => structuralRawBudget (structuralRawRequest r)) :=
    ⟨structuralRawMachine.program, by
      intro r
      simpa only [structuralOutput, structuralRawRequest_bit] using
        structuralRawMachine.realizes (structuralRawRequest r)⟩
  exact Program.WordFunction.pipe (structuralFormatterMachine B1 B2) g

end NearQuarticWires.StageMainMask
