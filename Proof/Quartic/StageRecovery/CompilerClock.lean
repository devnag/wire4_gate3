import Proof.Quartic.StageRecovery.TermsMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: the squared
structural Formula hint pays the token-count times token-work product,
including the real return across all original source bytes. -/
theorem ModFormulaRequest.cachedEvaluationCost_le (r : ModFormulaRequest) :
    cachedEvaluationCost r.formula ≤ 2000 * (r.hint + 1) := by
  let T := r.arity + r.formula.size +
    (formulaWord ⟨r.arity, r.formula⟩).length + natBitLength r.modulus + 10
  have hT : 10 ≤ T := by dsimp [T]; omega
  have hh : T ^ 2 ≤ r.hint := r.hint_sufficient
  have ht : (tokenStream (toks r.formula)).length ≤
      (formulaWord ⟨r.arity, r.formula⟩).length := by
    simp only [formulaWord, NearCubicGates.Close.Interfaces.listWord, tokenStream, List.length_append]
    omega
  have hN : (toks r.formula).length ≤ T := by
    have hn := tokens_length_le_stream r.formula
    dsimp [T]
    omega
  have hB : formulaTokenBound r.formula + 10 ≤ 2 * T := by
    dsimp [formulaTokenBound, T]
    omega
  have hprod := Nat.mul_le_mul hN hB
  have hsmall : T ≤ r.hint := (Nat.le_self_pow (by norm_num) T).trans hh
  have hL : (tokenStream (toks r.formula)).length ≤ r.hint := by dsimp [T] at hsmall; omega
  unfold cachedEvaluationCost
  nlinarith

/-- `prop:time`, paper/paper.tex: the setup hint
simultaneously pays the squares of arity and family dimensions, while
retaining the original Formula's actual squared structural hint. -/
theorem FamilyCompileRequest.clock_dimensions (r : FamilyCompileRequest) :
    r.source.arity ^ 2 ≤ r.setupHint ∧ r.source.arity ≤ r.setupHint ∧
      r.source.hint ≤ r.setupHint ∧ natBitLength r.source.modulus ≤ r.setupHint ∧
      r.family.width ≤ r.setupHint := by
  have hs := r.source.hint_sufficient
  have hstruct : r.source.arity + r.source.formula.size +
      (formulaWord ⟨r.source.arity, r.source.formula⟩).length + natBitLength r.source.modulus + 10 ≤
      r.source.hint := (Nat.le_self_pow (by norm_num) _).trans hs
  have hh : r.source.hint ≤ r.setupHint := by unfold FamilyCompileRequest.setupHint; omega
  have hV2 : r.source.arity ^ 2 ≤ r.setupHint := by unfold FamilyCompileRequest.setupHint; nlinarith
  have hw := r.setupHint_width
  exact ⟨hV2, (Nat.le_self_pow (by norm_num) _).trans hV2, hh, by omega, by omega⟩

/-- `prop:time`, paper/paper.tex: each actual
canonical monomial serializer has source cost linear in the squared
structural setup hint, including both support scans and coefficient bits. -/
theorem FamilyCompileRequest.monomialCost_le (r : FamilyCompileRequest) :
    monomialCost r.source.arity r.source.modulus ≤ 1000 * (r.setupHint + 1) := by
  obtain ⟨hV2, hV, _, hq, _⟩ := r.clock_dimensions
  unfold monomialCost
  have hzero : natBitLength 0 = 1 := rfl
  rw [hzero]
  nlinarith

/-- `prop:time`, paper/paper.tex: the actual native
family count has binary height controlled by the small setup hint. -/
theorem FamilyCompileRequest.family_count_bits (r : FamilyCompileRequest) :
    natBitLength (famPairs r.source.arity r.degree).length ≤ r.setupHint := by
  have hN : (famPairs r.source.arity r.degree).length ≤ 2 ^ (r.source.arity * r.degree) := by
    have hh := r.family_count_bound
    rw [famRecs_eq, List.length_map] at hh
    exact hh
  have hs := r.family_span_exponent
  have hw := r.setupHint_width
  apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega)
  exact hN.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- `prop:time`, paper/paper.tex: loading the
generated packet and returning across the original Formula source have
linear record-count cost with the same structural setup factor. -/
theorem FamilyCompileRequest.prepareCacheSteps_le (r : FamilyCompileRequest) :
    r.prepareCacheSteps ≤
      1000 * ((famPairs r.source.arity r.degree).length + 1) * (r.setupHint + 1) := by
  obtain ⟨_, hV, hhint, _, hW⟩ := r.clock_dimensions
  have hL := r.token_length_le
  have hNW := Nat.mul_le_mul_left (famPairs r.source.arity r.degree).length hW
  have hNL := Nat.mul_le_mul_left (famPairs r.source.arity r.degree).length hV
  unfold FamilyCompileRequest.prepareCacheSteps
  rw [famRecs_eq, List.length_map]
  nlinarith

/-- `prop:time`, paper/paper.tex: the literal
seven-field source header has a linear structural-hint parsing clock. -/
theorem FamilyCompileRequest.headerCost_le (r : FamilyCompileRequest) :
    StageGamma.readFieldsCost r.header ≤ 1000 * (r.setupHint + 1) := by
  have h := StageGamma.readFieldsCost_le r.header (r.setupHint + 2) r.header_bits
  have hlen : r.header.length = 7 := rfl
  rw [hlen] at h
  omega

/-- `prop:time`, paper/paper.tex: cold initialization,
header parsing and actual family loading contribute only an additive
linear family pass before coefficient computation. -/
theorem FamilyCompileRequest.coldCacheSteps_le (r : FamilyCompileRequest) :
    r.coldCacheSteps ≤
      3000 * ((famPairs r.source.arity r.degree).length + 1) * (r.setupHint + 1) := by
  have hh := r.headerCost_le
  have hp := r.prepareCacheSteps_le
  unfold FamilyCompileRequest.coldCacheSteps
  nlinarith

/-- `prop:time`, paper/paper.tex: actual cached
Formula evaluations and every quadratic sequential scan together have
the sharp quadratic-family source clock times one setup-hint factor. -/
theorem FamilyCompileRequest.coefficientSteps_le (r : FamilyCompileRequest) :
    r.coefficientSteps ≤
      5000 * ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) := by
  let N := (famPairs r.source.arity r.degree).length
  let H := r.setupHint + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hdim := r.clock_dimensions
  have hcache : cachedEvaluationCost r.source.formula ≤ 2000 * H :=
    r.source.cachedEvaluationCost_le.trans (Nat.mul_le_mul_left _ (by dsimp [H]; omega))
  have hd : coefficientDriverCost r.source.arity N ≤ 100 * (N + 1) ^ 2 * H :=
    (coefficientDriverCost_le _ _).trans (Nat.mul_le_mul_left _ (by dsimp [H]; omega))
  have hm := Nat.mul_le_mul_left N hcache
  have hN : N ≤ (N + 1) ^ 2 := by nlinarith
  have hNH := Nat.mul_le_mul_right H hN
  have hNH0 : N ≤ N * H := Nat.le_mul_of_pos_right _ hH
  have hunit : 1 ≤ (N + 1) ^ 2 * H := by
    have hpos : 0 < (N + 1) ^ 2 * H := by positivity
    omega
  change N * (cachedEvaluationCost r.source.formula + 20) + 4 +
    (2 * N + 3 + coefficientDriverCost r.source.arity N + 1) + 1 ≤ _
  change _ ≤ 5000 * (N + 1) ^ 2 * H
  nlinarith

/-- `prop:time`, paper/paper.tex: the actual complete
canonical Terms writer has a linear family pass times one setup-hint
factor, including the runtime-computed list header. -/
theorem FamilyCompileRequest.termsCodecCost_le (r : FamilyCompileRequest) :
    termsCodecCost r.source.arity r.source.modulus (famPairs r.source.arity r.degree).length ≤
      2000 * ((famPairs r.source.arity r.degree).length + 1) * (r.setupHint + 1) := by
  have hm := r.monomialCost_le
  have hn := r.family_count_bits
  have hprod := Nat.mul_le_mul_left (famPairs r.source.arity r.degree).length hm
  unfold termsCodecCost
  nlinarith

/-- `prop:time`, paper/paper.tex: the entire actual
cold source-to-canonical-Terms program has the literal quadratic family
census and one structural setup-hint factor before physical compilation. -/
theorem FamilyCompileRequest.compileTermsSteps_le (r : FamilyCompileRequest) :
    r.compileTermsSteps ≤
      20000 * ((famPairs r.source.arity r.degree).length + 1) ^ 2 * (r.setupHint + 1) := by
  let N := (famPairs r.source.arity r.degree).length
  let H := r.setupHint + 1
  have hc := r.coldCacheSteps_le
  have hp := r.coefficientSteps_le
  have ht := r.termsCodecCost_le
  change r.coldCacheSteps ≤ 3000 * (N + 1) * H at hc
  change r.coefficientSteps ≤ 5000 * (N + 1) ^ 2 * H at hp
  change termsCodecCost r.source.arity r.source.modulus N ≤ 2000 * (N + 1) * H at ht
  have hN : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hNH := Nat.mul_le_mul_right H hN
  have hNsmall : N ≤ (N + 1) * H := by dsimp [H]; nlinarith
  have hunit : 1 ≤ (N + 1) ^ 2 * H := by
    have hpos : 0 < (N + 1) ^ 2 * H := by dsimp [H]; positivity
    omega
  change (r.coldCacheSteps + r.coefficientSteps + 1) +
    ((2 * N + 3) + termsCodecCost r.source.arity r.source.modulus N + 1) + 1 ≤ _
  change _ ≤ 20000 * (N + 1) ^ 2 * H
  nlinarith

end NearQuarticWires.StageRecovery
