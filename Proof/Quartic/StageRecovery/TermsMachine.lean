import Proof.Quartic.StageRecovery.CompileTerms

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the actual cache
stage input retains the original Formula source before the generated
native family packet, without repeating either one per support. -/
def FamilyCompileRequest.cacheInput (r : FamilyCompileRequest) : List Bool :=
  r.word ++ r.family.output

/-- `prop:time`, paper/paper.tex: appending the
generated family leaves the original small structural leading hint
unchanged; neither family count nor a walk index controls binary width. -/
theorem FamilyCompileRequest.cacheInput_leading (r : FamilyCompileRequest) :
    leadOnes r.cacheInput = natBitLength r.setupHint := by
  unfold FamilyCompileRequest.cacheInput FamilyCompileRequest.word
  simpa only [List.append_assoc] using
    NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.setupHint
      (natWord r.degree ++ natWord (tokenStream (toks r.source.formula)).length ++
        r.source.word ++ r.family.output)

/-- `prop:time`, paper/paper.tex: actual cache-stage
workspace is derived solely from its literal leading structural hint. -/
theorem FamilyCompileRequest.cache_context_width (r : FamilyCompileRequest) :
    64 * (r.setupHint + 1) ≤ (ctxOf packetCallee pointSizes r.cacheInput).Wd := by
  change 64 * (r.setupHint + 1) ≤ 2 ^ (1 * leadOnes r.cacheInput) * 64
  rw [r.cacheInput_leading, Nat.one_mul]
  have h := lt_natBitLength r.setupHint
  omega

/-- `prop:time`, paper/paper.tex: the canonical
modular Terms machine pays the compiled cold source clock and all
actual input, store and output cleanup on the native multitape model. -/
noncomputable def FamilyCompileRequest.termsCacheBudget (r : FamilyCompileRequest) : ℕ :=
  langBudget packetCallee pointSizes VV MM r.cacheInput (3 * r.compileTermsSteps + 2)

/-- `lem:print`, paper/paper.tex: an actual ordinary
word function maps the literal retained Formula and generated family
to the complete framed canonical modular Terms word. -/
noncomputable def termsCacheWordFunction :
    WordFunction FamilyCompileRequest FamilyCompileRequest.cacheInput
      (fun r => frame (termsWord (boundedModTerms r.source.modulus r.source.formula r.degree)))
      FamilyCompileRequest.termsCacheBudget :=
  wordFunction_of_lang FamilyCompileRequest.cacheInput
    (fun r => frame (termsWord (boundedModTerms r.source.modulus r.source.formula r.degree)))
    packetCallee pointSizes (OutputFrame.framedProgram compileTermsProgram)
    (fun r => 3 * r.compileTermsSteps + 2) (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := compileTermsProgram_spec
        (ctxOf packetCallee pointSizes r.cacheInput) r rfl r.cache_context_width
      have hf := OutputFrame.framedProgram_spec he
      exact ⟨OutputFrame.framedState b, 3 * n + 2, hf,
        by simpa [OutputFrame.framedState] using congrArg frame ho, by omega⟩) (by
      intro r
      have h := r.cache_context_width
      change 1 ≤ (ctxOf packetCallee pointSizes r.cacheInput).Wd
      omega)

/-- `prop:time`, paper/paper.tex: original family
generation and complete modular coefficient recovery have additive
physical costs, with one source retention and one final canonical output. -/
noncomputable def FamilyCompileRequest.modularTermsBudget (r : FamilyCompileRequest) : ℕ :=
  4 * r.retainedFamilyBudget + 4 * r.termsCacheBudget + 12

/-- `lem:print`, paper/paper.tex: the genuine cold
modular Formula compiler starts from the original serialized Formula
request and emits canonical Terms without any precomputed coefficient,
support-family input, raw polynomial value or division in the residue ring. -/
noncomputable def modularTermsWordFunction :
    WordFunction FamilyCompileRequest FamilyCompileRequest.word
      (fun r => frame (termsWord (boundedModTerms r.source.modulus r.source.formula r.degree)))
      FamilyCompileRequest.modularTermsBudget :=
  Program.WordFunction.pipe retainedFamilyWordFunction termsCacheWordFunction

end NearQuarticWires.StageRecovery
