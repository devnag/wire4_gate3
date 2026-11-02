import Proof.Quartic.StageRecovery.FamilyFields
import Proof.Quartic.StageRecovery.FamilyPrepare
import Proof.Quartic.StageRecovery.FamilyHeaderBounds
import Proof.Quartic.StageRecovery.OutputFrame
import Proof.Gates.Cells.Prelude

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the cold original
Formula source is parsed and its complete finite native family input
is physically constructed from initialized binary registers. -/
def familyFormatterProgram : St VV MM :=
  .seq initP (.seq familyHeaderProgram (.seq prepareFamilyProgram familyFieldsProgram))

/-- `prop:time`, paper/paper.tex: the formatter clock
includes initialization, every original metadata field, binary arithmetic,
all finite setup bits and both unary dimension fields. -/
def FamilyCompileRequest.formatterSteps (r : FamilyCompileRequest) : ℕ :=
  5 + (StageGamma.readFieldsCost r.header +
    ((7 * r.source.arity + 34) +
      (1000 * (r.family.width + r.family.arity + r.family.degree + 1)) + 1) + 1) + 1

/-- `lem:print`, paper/paper.tex: an actual cold source
program constructs exactly the native family-generator word, with no
precomputed setup fields or support lists in the request. -/
theorem familyFormatterProgram_spec (C : Ctx) (r : FamilyCompileRequest)
    (hin : C.inp = r.word) (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd) :
    Hs C familyFormatterProgram (a0 : DS VV MM) r.formatterSteps (fun b => b.out = r.family.word) := by
  have hW : 2 ≤ C.Wd := by omega
  have hfpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hfields : ∀ v ∈ r.header, natBitLength v + 2 ≤ C.Wd := by
    intro v hv
    have h := r.header_bits v hv
    omega
  have hdim : r.source.arity + r.degree + 10 ≤ C.Wd := by
    have h := r.setupHint_width
    dsimp [FamilyCompileRequest.family, FamilyRequest.width] at h
    omega
  have hfield : r.family.width < 2 ^ C.Wd := by
    have h := r.setupHint_width
    omega
  unfold familyFormatterProgram FamilyCompileRequest.formatterSteps
  refine Hs.seq (t2 := StageGamma.readFieldsCost r.header +
    ((7 * r.source.arity + 34) +
      (1000 * (r.family.width + r.family.arity + r.family.degree + 1)) + 1) + 1)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    fun a ⟨hc, _, _, hip, hout, _, _, _, _⟩ => ?_
  refine Hs.seq (t2 := (7 * r.source.arity + 34) +
    (1000 * (r.family.width + r.family.arity + r.family.degree + 1)) + 1)
    (familyHeaderProgram_spec C a hc r
      (by rw [hip]; simpa only [a0, List.drop_zero] using hin) hfields)
    fun b ⟨hbD, hbV, _, _, _, _, _, _, hbr, hbc, _⟩ => ?_
  refine Hs.seq (t2 := 1000 * (r.family.width + r.family.arity + r.family.degree + 1))
    (prepareFamilyProgram_spec C b hbc r.family hbV hbD hdim)
    fun d ⟨hdw, hdb, hdm, hdsh, hdc, hdf⟩ => ?_
  refine (familyFieldsProgram_spec C d hdc r.family
    (by rw [hdf _ (by decide)]; exact hbV)
    (by rw [hdf _ (by decide)]; exact hbD) hdw hdb hdm hfield hW).mono le_rfl ?_
  rintro e ⟨heo, _, _, _⟩
  have hdo : d.out = b.out := (Same.of_sh hdsh).out
  have hbo : b.out = a.out := congrArg Prod.fst hbr
  rw [hdo, hbo, hout] at heo
  exact heo

/-- `prop:time`, paper/paper.tex: the exact cold
ordinary formatter pays its actual structural workspace and every
framing instruction before the separate native family computation. -/
noncomputable def FamilyCompileRequest.formatterBudget (r : FamilyCompileRequest) : ℕ :=
  langBudget packetCallee pointSizes VV MM r.word (3 * r.formatterSteps + 2)

/-- `lem:print`, paper/paper.tex: a genuine uniform
ordinary word function maps the literal source Formula request to the
exact framed native family input, ready for physical sequential composition. -/
noncomputable def familyFormatterWordFunction :
    WordFunction FamilyCompileRequest FamilyCompileRequest.word
      (fun r => frame r.family.word) FamilyCompileRequest.formatterBudget :=
  wordFunction_of_lang FamilyCompileRequest.word (fun r => frame r.family.word)
    packetCallee pointSizes (OutputFrame.framedProgram familyFormatterProgram)
    (fun r => 3 * r.formatterSteps + 2) (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := familyFormatterProgram_spec
        (ctxOf packetCallee pointSizes r.word) r rfl r.context_width
      have hf := OutputFrame.framedProgram_spec he
      exact ⟨OutputFrame.framedState b, 3 * n + 2, hf, by simpa [OutputFrame.framedState] using congrArg frame ho,
        by omega⟩) (by
      intro r
      have h := r.context_width
      change 1 ≤ (ctxOf packetCallee pointSizes r.word).Wd
      omega)

end NearQuarticWires.StageRecovery
