import Proof.Quartic.StageMainMask.StructuralPrepare
import Proof.Quartic.StageMain.MarkedOutput

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `def:mask`, paper/paper.tex: the canonical
structural source contains exactly the selected block size and the
original pattern codes, not an alternative ordering of the cell. -/
theorem structuralRawRequest_word {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    (structuralRawRequest r).word = callWord r.call ++
      [r.selected.1.dstar, r.selected.1.b, r.selected.1.r,
        r.left.val, r.right.val].flatMap natWord := by
  have hb := (Cells.prepare_spec _ r.selected.1 r.selected.2).star_b
  change callWord r.call ++
    [(r.selected.1).dstar,
      (Builder.star r.call (Cells.prepare_spec _ r.selected.1 r.selected.2)).b,
      r.selected.1.r, r.left.val, r.right.val].flatMap natWord = _
  rw [hb]

/-- `def:mask` and `prop:time`, paper/paper.tex: all printed metadata bit lengths are bounded by the literal
prepared source word, including the actual large pattern codes. -/
theorem structural_metadata_bits {B1 B2 : ℕ} (r : StructuralRequest B1 B2) :
    ∀ value ∈ [r.selected.1.dstar, r.selected.1.b, r.selected.1.r,
      r.left.val, r.right.val], natBitLength value ≤ (structuralWord r).length := by
  have hp : (Program.parametersWord r.selected.1).length ≤ (structuralWord r).length := by
    rw [structuralWord, prepWord_eq_compact r.dispatched]
    simp only [compactInput, preparedPrefixWord, List.length_append, List.length_cons]
    omega
  have hparam : ∀ value ∈ [r.selected.1.dstar, r.selected.1.b, r.selected.1.r],
      natBitLength value ≤ (structuralWord r).length := by
    intro value hv
    apply (parameter_bitLength_le_word r.selected.1 value ?_).trans hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;>
      simp [parameterHeadFields, parameterHeadScalars]
  intro value hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · exact hparam _ (by simp)
  · exact hparam _ (by simp)
  · exact hparam _ (by simp)
  · have h := NearCubicGates.Close.Dispatch.natBitLength_le_len r.left.val
    simp only [structuralWord, List.length_append]
    omega
  · have h := NearCubicGates.Close.Dispatch.natBitLength_le_len r.right.val
    simp only [structuralWord, List.length_append]
    omega

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: the full finite-source formatter reads the
actual preparation prefix and prints the raw structural scan request. -/
def structuralFormatterRaw : St VV MM := .seq structuralPrepare structuralPrint

/-- `prop:time`, paper/paper.tex: both original-source
acquisition and binary request output are included in the formatter. -/
noncomputable def structuralFormatterSteps {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : ℕ :=
  structuralPrepareSteps r + 20 * (callWord r.call).length +
    400 * (structuralWord r).length + 3001

/-- `def:mask`, Step 4 of `sec:algorithm`, and `prop:time`,
paper/paper.tex: the literal
prepared call is converted to the exact raw scan request by a physical
parser and printer, with all original source acquisition charged. -/
theorem structuralFormatterRaw_run {B1 B2 : ℕ} (C : Ctx) (r : StructuralRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = structuralWord r ++ rest)
    (hwidth : (structuralWord r).length + 2 ≤ C.Wd) (h64 : 64 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C structuralFormatterRaw a (structuralFormatterSteps r) (fun b =>
      b.out = a.out ++ (structuralRawRequest r).word) := by
  have hcall : (callWord r.call).length ≤ (structuralWord r).length := by
    rw [structuralWord, prepWord_eq_compact r.dispatched]
    simp only [compactInput, preparedPrefixWord, List.length_append, List.length_cons]
    omega
  unfold structuralFormatterRaw
  refine (Hs.seq (t2 := 20 * (callWord r.call).length + 400 * (structuralWord r).length + 3000)
    (structuralPrepare_run C r rest a hc hin hwidth hempty) ?_).mono
      (by unfold structuralFormatterSteps; omega) (fun _ h => h)
  rintro b ⟨hbs, hblen, hbu, hbv, hbout, hbc⟩
  refine (structuralPrint_run C r.call r.selected.1 r.left.val r.right.val
    (structuralWord r).length b hbc hbs hblen hbu hbv h64 hwidth
    (lt_trans (by omega) Nat.lt_two_pow_self) (structural_metadata_bits r)).mono le_rfl ?_
  rintro d ⟨hdout, _hdip, _hdram, _hdc⟩
  rw [hdout, hbout, structuralRawRequest_word]

end NearQuarticWires.StageMainMask
