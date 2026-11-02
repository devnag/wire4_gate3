import Proof.Quartic.StageRecovery.CoefficientPipeline
import Proof.Quartic.StageRecovery.TermsCodec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the coefficient
output pass physically rewinds its two aligned source stores. -/
def rewindTermStreamsProgram : St VV MM :=
  .seq (.op (.rwM outerSupports)) (.op (.rwM coefficientStore))

/-- `lem:print`, paper/paper.tex: the exact state
after the two paid physical term-stream head returns. -/
def rewindTermStreams (a : DS VV MM) : DS VV MM :=
  (a.rew outerSupports).rew coefficientStore

/-- `prop:time`, paper/paper.tex: the actual
term-stream return pays both advancing record-store cursors. -/
theorem rewindTermStreamsProgram_spec (C : Ctx) (a : DS VV MM) (N : ℕ)
    (hs : a.rc outerSupports = N) (hc : a.rc coefficientStore = N) :
    Hs C rewindTermStreamsProgram a (2 * N + 3) (fun b => b = rewindTermStreams a) := by
  unfold rewindTermStreamsProgram
  refine (Hs.seq (t1 := N + 1) (t2 := N + 1)
    ((hs_rwM C outerSupports a).mono (by rw [hs]) (fun _ h => h))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  exact (hs_rwM C coefficientStore _).mono
    (by simpa (config := {decide := true}) [DS.rew] using hc.le) (fun _ h => h)

/-- `lem:print`, paper/paper.tex: actual support and
coefficient tapes become aligned at zero after their paid rewinds. -/
theorem TermStreamAt.rewind {records : List (ℕ × ℕ)} {k : ℕ} {a : DS VV MM}
    (h : TermStreamAt records k a) : TermStreamAt records 0 (rewindTermStreams a) := by
  exact ⟨h.supports, h.coefficients,
    by simp (config := {decide := true}) [rewindTermStreams, DS.rew],
    by simp (config := {decide := true}) [rewindTermStreams, DS.rew]⟩

/-- `lem:print`, paper/paper.tex: the cold original
source is expanded modulo the actual modulus and serialized directly
as canonical Terms, without an unreduced polynomial-value premise. -/
def compileTermsProgram : St VV MM :=
  .seq coldCoefficientProgram (.seq rewindTermStreamsProgram emitTermsProgram)

/-- `prop:time`, paper/paper.tex: cold source,
cache, coefficient scans, record rewinds and canonical output clocks add. -/
def FamilyCompileRequest.compileTermsSteps (r : FamilyCompileRequest) : ℕ :=
  let N := (famPairs r.source.arity r.degree).length
  (r.coldCacheSteps + r.coefficientSteps + 1) +
    ((2 * N + 3) + termsCodecCost r.source.arity r.source.modulus N + 1) + 1

/-- `lem:print`, paper/paper.tex: the genuine cold
multitape program computes exactly the complete canonical modular Terms
from the original Formula word and actual native generated family. -/
theorem compileTermsProgram_spec (C : Ctx) (r : FamilyCompileRequest)
    (hin : C.inp = r.word ++ r.family.output)
    (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd) :
    Hs C compileTermsProgram (a0 : DS VV MM) r.compileTermsSteps (fun b =>
      b.out = termsWord (boundedModTerms r.source.modulus r.source.formula r.degree)) := by
  let V := r.source.arity
  let q := r.source.modulus
  let entries := boundedFormulaCache q r.source.formula r.degree
  let records := cachedTermRecords q V entries
  let N := (famPairs V r.degree).length
  have hq : 0 < q := by have := r.source.modulus_ge_two; omega
  have hentries : entries.length = N := by simp [entries, boundedFormulaCache, pointEntries, N, V]
  have hrecords : records.length = N := by simp only [records, cachedTermRecords, List.length_map, hentries]
  obtain ⟨_, hNfit, _, _, _⟩ := r.family_parser_bounds C hwidth
  have hNrecs : (famRecs V r.degree).length = N := by rw [famRecs_eq, List.length_map]
  have hNsmall : N < 2 ^ C.Wd := by rw [← hNrecs]; exact hNfit
  have hNpow : N ≤ 2 ^ (V * r.degree) := by rw [← hNrecs]; exact r.family_count_bound
  have hspan := r.family_span_exponent
  have hstruct := r.setupHint_width
  have hbitsN : natBitLength N ≤ r.setupHint := by
    apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega)
    exact hNpow.trans_lt (Nat.pow_lt_pow_right (by decide) (by dsimp [V]; omega))
  have hcore := r.source.core_width
  have hbitq : natBitLength q + 2 ≤ C.Wd := by
    have hmul : natBitLength q ≤ ((toks r.source.formula).length + 3) * natBitLength q :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hh : r.source.hint ≤ r.setupHint := by unfold FamilyCompileRequest.setupHint; omega
    change _ ∧ ((toks r.source.formula).length + 3) * natBitLength q ≤ _ at hcore
    omega
  have hVsmall : V + 3 < 2 ^ C.Wd := by
    have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    dsimp [FamilyCompileRequest.family, FamilyRequest.width] at hstruct
    dsimp [V]
    omega
  have hzero : natBitLength 0 + 2 < 2 ^ C.Wd := by
    have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    norm_num [natBitLength]
    omega
  have hqb : natBitLength q + 2 < 2 ^ C.Wd := hbitq.trans_lt Nat.lt_two_pow_self
  have hNb : natBitLength N + 2 < 2 ^ C.Wd := by
    have hp : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
    omega
  have hvalues : ∀ p ∈ records, p.2 < q := by
    intro p hp
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hp
    exact cachedMobFold_lt q V e.1 e.2.1 0 entries hq hq
  unfold compileTermsProgram FamilyCompileRequest.compileTermsSteps
  refine Hs.seq (t2 := (2 * N + 3) + termsCodecCost V q N + 1)
    (coldCoefficientProgram_spec C r hin hwidth)
    fun b ⟨hbc, hbm, hbcst, hbout, hbV, _, hbN⟩ => ?_
  have hstream : TermStreamAt records N b := by
    refine ⟨?_, ?_, hbm.supportCursor, hbm.coefficientCursor⟩
    · rw [hbm.supports]
      simp only [records, cachedTermRecords, List.map_map]
      rfl
    · rw [hbc]
      simp only [records, cachedTermRecords, cachedCoefficients, List.map_map]
      rfl
  refine Hs.seq (t2 := termsCodecCost V q N)
    (rewindTermStreamsProgram_spec C b N hstream.supportCursor hstream.coefficientCursor)
    fun d hd => ?_
  subst d
  refine (emitTermsProgram_spec C (rewindTermStreams b) ⟨hbcst.z, hbcst.one, hbcst.two⟩
    V q records hstream.rewind
    (by change b.env arityVar = V; exact hbV)
    (by change b.env cacheCountVar = records.length; rw [hrecords]; exact hbN)
    hvalues (by omega) hVsmall hzero hqb
    (by rw [hrecords]; exact hNsmall) (by rw [hrecords]; exact hNb)).mono
      (by rw [hrecords]) ?_
  rintro e ⟨heo, _⟩
  have hterms : termsOfRecords V records = boundedModTerms q r.source.formula r.degree :=
    termsOfRecords_cached q hq r.source.formula r.degree
  simpa only [rewindTermStreams, DS.rew, hbout, List.nil_append,
    hterms] using heo

end NearQuarticWires.StageRecovery
