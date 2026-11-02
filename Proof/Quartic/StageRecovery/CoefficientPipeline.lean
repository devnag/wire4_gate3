import Proof.Quartic.StageRecovery.FamilyColdReady
import Proof.Quartic.StageRecovery.BoundedCoefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: every original
support is evaluated once before the actual quadratic coefficient pass. -/
def cacheCoefficientProgram : St VV MM :=
  .seq buildCacheProgram (.seq prepareCoefficientProgram coefficientDriverProgram)

/-- `prop:time`, paper/paper.tex: the cache and
coefficient clocks add, including their actual metadata rewinds. -/
def FamilyCompileRequest.coefficientSteps (r : FamilyCompileRequest) : ℕ :=
  let N := (famPairs r.source.arity r.degree).length
  N * (cachedEvaluationCost r.source.formula + 20) + 4 +
    (2 * N + 3 + coefficientDriverCost r.source.arity N + 1) + 1

/-- `lem:print`, paper/paper.tex: the genuinely loaded
family and original Formula bytes suffice to compute all modular
coefficients in order, without supplied evaluations or coefficients. -/
theorem cacheCoefficientProgram_spec (C : Ctx) (r : FamilyCompileRequest)
    (a : DS VV MM) (hready : FamilyCacheReady r a.ip a)
    (hin : C.inp.drop a.ip = tokenStream (toks r.source.formula) ++ r.family.output)
    (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd) :
    Hs C cacheCoefficientProgram a r.coefficientSteps (fun b =>
      b.ram coefficientStore = cachedCoefficients r.source.modulus r.source.arity
        (boundedFormulaCache r.source.modulus r.source.formula r.degree) ∧
      MobOuterAt r.source.modulus r.source.arity
        (boundedFormulaCache r.source.modulus r.source.formula r.degree)
        (famPairs r.source.arity r.degree).length b ∧ Cst b ∧ b.out = [] ∧
      b.env arityVar = r.source.arity ∧ b.env modulusVar = r.source.modulus ∧
      b.env cacheCountVar = (famPairs r.source.arity r.degree).length) := by
  let V := r.source.arity
  let q := r.source.modulus
  let F := r.source.formula
  let points := famPairs V r.degree
  let entries := pointEntries q F points
  let N := points.length
  have hq : 2 ≤ q := r.source.modulus_ge_two
  have hcore := r.source.core_width
  change formulaTokenBound F + 5 ≤ 4 * (r.source.hint + 1) ∧
    ((toks F).length + 3) * natBitLength q ≤ 4 * (r.source.hint + 1) at hcore
  have hhint : r.source.hint ≤ r.setupHint := by unfold FamilyCompileRequest.setupHint; omega
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  obtain ⟨_, hNfit, hLfit, _, _⟩ := r.family_parser_bounds C hwidth
  have hcountfit : (toks F).length < 2 ^ C.Wd :=
    (tokens_length_le_stream F).trans_lt hLfit
  have hfwidth : formulaTokenBound F + 5 ≤ C.Wd := by omega
  have hVwidth : V + 2 ≤ C.Wd := by
    dsimp [formulaTokenBound, V, F] at hfwidth ⊢
    omega
  have hdepth : q ^ ((toks F).length + 3) ≤ 2 ^ C.Wd := by
    calc q ^ ((toks F).length + 3) ≤
        (2 ^ natBitLength q) ^ ((toks F).length + 3) :=
          Nat.pow_le_pow_left (lt_natBitLength _).le _
      _ = 2 ^ (natBitLength q * ((toks F).length + 3)) := by rw [pow_mul]
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by
        rw [Nat.mul_comm]; omega)
  have hN : (famRecs V r.degree).length = N := by
    rw [famRecs_eq, List.length_map]
  have hentries : entries.length = N := by simp [entries, pointEntries, N]
  have hprefix : CachePrefix entries 0 a := by
    have hempty : ∀ m ∈ [cacheSupports, cacheParities, cacheValues, outerSupports, outerParities],
        a.ram m = [] ∧ a.rc m = 0 := by
      intro m hm
      exact hready.others m (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide)
    exact ⟨by simpa using (hempty _ (by simp)).1,
      by simpa using (hempty _ (by simp)).1,
      by simpa using (hempty _ (by simp)).1,
      by simpa using (hempty _ (by simp)).1,
      by simpa using (hempty _ (by simp)).1,
      fun m hm => (hempty m hm).2⟩
  have hrecords : a.ram familyRecordStore = points.map (packedFamilyRecord V) := by
    rw [hready.records, famRecs_eq]
    rfl
  have hfamilyn : a.env cacheCountVar = N := hready.count.trans hN
  have hNsmall : N < 2 ^ C.Wd := by rw [← hN]; exact hNfit
  have hqfit : 2 * q ≤ 2 ^ C.Wd := by
    have hb : 1 ≤ natBitLength q := by unfold natBitLength; omega
    have hexp : natBitLength q + 1 ≤ C.Wd := by
      have hp := hcore.2
      have hn : 3 * natBitLength q ≤ ((toks F).length + 3) * natBitLength q :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    calc 2 * q ≤ 2 * 2 ^ natBitLength q := Nat.mul_le_mul_left _ (lt_natBitLength _).le
      _ = 2 ^ (natBitLength q + 1) := by ring
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) hexp
  unfold cacheCoefficientProgram FamilyCompileRequest.coefficientSteps
  refine Hs.seq (t2 := 2 * N + 3 + coefficientDriverCost V N + 1)
    (buildCacheProgram_spec C a hready.constants F q points hprefix hrecords hready.recordCursor
      hready.radix (fun p hp => (famPairs_mem V r.degree p hp).1) hq hready.modulus
      hready.tokens hcountfit r.family.output hin hfwidth hVwidth hdepth
      hready.tokenLength hLfit hfamilyn hNsmall)
    fun b ⟨hcache, _, _, hbc, hbcc, _, hbcst, hbf, hbout⟩ => ?_
  have hcoeff0 := hready.others coefficientStore (by decide)
  have hcacheready : CachePrefix entries entries.length b := by
    simpa only [hentries] using hcache
  have hstart := CachePrefix.driverReady (q := q) (V := V) hcacheready
    (hbc.trans hcoeff0.1) (hbcc.trans hcoeff0.2)
  have hcs : b.rc outerSupports = N := by
    simpa only [hentries] using hcache.cursors outerSupports (by simp)
  have hcp : b.rc outerParities = N := by
    simpa only [hentries] using hcache.cursors outerParities (by simp)
  refine Hs.seq (t2 := coefficientDriverCost V N)
    (prepareCoefficientProgram_spec C b N hcs hcp) fun d hd => ?_
  subst d
  refine (coefficientDriverProgram_spec C (prepareCoefficient b) ⟨hbcst.z, hbcst.one, hbcst.two⟩ q V entries hstart
    (by change b.env arityVar = V; rw [hbf _ (by decide)]; exact hready.arity)
    (by change b.env modulusVar = q; rw [hbf _ (by decide)]; exact hready.modulus)
    (by omega) hqfit
    (boundedFormulaCache_values q (by omega) F r.degree)
    (by omega) (by omega)
    (by change b.env cacheCountVar = entries.length
        rw [hbf _ (by decide)]; simpa only [hentries] using hfamilyn)
    (by simpa only [hentries] using hNsmall)).mono (by rw [hentries]) ?_
  rintro e ⟨hec, hem, hecst, hef, heout⟩
  refine ⟨hec, ?_, hecst, heout.trans (hbout.trans hready.output), ?_, ?_, ?_⟩
  · change MobOuterAt q V entries N e
    simpa only [hentries] using hem
  · rw [hef _ (by decide)]
    change b.env arityVar = V
    rw [hbf _ (by decide)]
    exact hready.arity
  · rw [hef _ (by decide)]
    change b.env modulusVar = q
    rw [hbf _ (by decide)]
    exact hready.modulus
  · rw [hef _ (by decide)]
    change b.env cacheCountVar = N
    rw [hbf _ (by decide)]
    exact hfamilyn

/-- `lem:print`, paper/paper.tex: the entire retained
source-to-coefficient program starts with no initialized registers or
preloaded work tapes. -/
def coldCoefficientProgram : St VV MM :=
  .seq coldFamilyCacheProgram cacheCoefficientProgram

/-- `lem:print`, paper/paper.tex: the literal original
source and generated native packet produce the complete ordered
coefficient bank on the actual cold multitape machine. -/
theorem coldCoefficientProgram_spec (C : Ctx) (r : FamilyCompileRequest)
    (hin : C.inp = r.word ++ r.family.output)
    (hwidth : 64 * (r.setupHint + 1) ≤ C.Wd) :
    Hs C coldCoefficientProgram (a0 : DS VV MM)
      (r.coldCacheSteps + r.coefficientSteps + 1) (fun b =>
        b.ram coefficientStore = cachedCoefficients r.source.modulus r.source.arity
          (boundedFormulaCache r.source.modulus r.source.formula r.degree) ∧
        MobOuterAt r.source.modulus r.source.arity
          (boundedFormulaCache r.source.modulus r.source.formula r.degree)
          (famPairs r.source.arity r.degree).length b ∧ Cst b ∧ b.out = [] ∧
        b.env arityVar = r.source.arity ∧ b.env modulusVar = r.source.modulus ∧
        b.env cacheCountVar = (famPairs r.source.arity r.degree).length) := by
  unfold coldCoefficientProgram
  refine Hs.seq (t2 := r.coefficientSteps) (coldFamilyCacheProgram_spec C r hin hwidth)
    fun a ha => ?_
  have hready : FamilyCacheReady r a.ip a := by
    rw [ha.sourcePosition]
    exact ha
  refine cacheCoefficientProgram_spec C r a hready ?_ hwidth
  rw [ha.sourcePosition, hin, r.word_eq_header]
  simp only [List.append_assoc, List.drop_left]

end NearQuarticWires.StageRecovery
