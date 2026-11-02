import Proof.Quartic.StageRecovery.MobRewind
import Proof.Quartic.StageRecovery.DenseCoefficients
import Proof.Gates.Expand.MobVal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the integer summand
represented by one cached modular update. -/
def cachedSummand (V s parity : ℕ) (e : CachedValue) : ℤ :=
  if setOf V e.1 ⊆ setOf V s then
    if parity = e.2.1 then (e.2.2 : ℤ) else -(e.2.2 : ℤ)
  else 0

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
subtracting a bounded residue from its positive modulus represents its
integer additive inverse, even when the residue is zero. -/
theorem natModNeg_modEq (q value : ℕ) (hv : value ≤ q) :
    (((q - value) % q : ℕ) : ℤ) ≡ -(value : ℤ) [ZMOD (q : ℤ)] := by
  rw [Int.natCast_mod, Nat.cast_sub hv]
  have hq : (q : ℤ) ≡ 0 [ZMOD (q : ℤ)] := by
    unfold Int.ModEq
    simp
  exact (Int.mod_modEq _ _).trans (by simpa using hq.sub (Int.ModEq.refl (value : ℤ)))

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
one checked finite update is congruent to its literal signed integer
summand; no inverse or prime-characteristic assumption is used. -/
theorem cachedMobStep_modEq (q V s parity acc : ℕ) (e : CachedValue) (hv : e.2.2 ≤ q) :
    (cachedMobStep q V s parity acc e : ℤ) ≡
      (acc : ℤ) + cachedSummand V s parity e [ZMOD (q : ℤ)] := by
  by_cases hs : setOf V e.1 ⊆ setOf V s
  · by_cases hp : parity = e.2.1
    · simp only [cachedMobStep, signedMobStep, hs, decide_true, if_true, hp,
        cachedSummand, Int.natCast_mod, Nat.cast_add]
      exact Int.mod_modEq _ _
    · simp only [cachedMobStep, signedMobStep, hs, decide_true, if_true, hp, decide_false,
        Bool.false_eq_true, if_false, cachedSummand, Int.natCast_mod, Nat.cast_add]
      exact (Int.mod_modEq _ _).trans ((Int.ModEq.refl (acc : ℤ)).add (natModNeg_modEq q e.2.2 hv))
  · simp only [cachedMobStep, signedMobStep, hs, decide_false, Bool.false_eq_true,
      if_false, cachedSummand, add_zero]
    exact Int.ModEq.refl _

/-- `lem:print`, paper/paper.tex: the actual scan's
finite fold represents the entire signed inclusion–exclusion sum. -/
theorem cachedMobFold_modEq (q V s parity acc : ℕ) (entries : List CachedValue)
    (hvalues : ∀ e ∈ entries, e.2.2 ≤ q) :
    ((entries.foldl (cachedMobStep q V s parity) acc : ℕ) : ℤ) ≡
      (acc : ℤ) + (entries.map (cachedSummand V s parity)).sum [ZMOD (q : ℤ)] := by
  induction entries generalizing acc with
  | nil => exact Int.ModEq.refl _
  | cons e entries ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      refine (ih _ (fun x hx => hvalues x (by simp [hx]))).trans ?_
      have hh := (cachedMobStep_modEq q V s parity acc e (hvalues e (by simp))).add_right
        ((entries.map (cachedSummand V s parity)).sum)
      simpa only [add_assoc] using hh

/-- `lem:print`, paper/paper.tex: the original finite
family supplies one cached point value and its actual degree parity. -/
def formulaCache {V : ℕ} (q : ℕ) (F : Formula V) : List CachedValue :=
  (famPairs V F.degree).map fun p => (p.1, p.2 % 2, (modAlg q p.1).eval F)

/-- `lem:print`, paper/paper.tex: every cached formula
value is reduced before it is used by any coefficient scan. -/
theorem formulaCache_values {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V) :
    ∀ e ∈ formulaCache q F, e.2.2 < q := by
  intro e he
  unfold formulaCache at he
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
  exact (modAlg q p.1).eval_lt (modAlg_closed q p.1 hq) F

/-- `lem:print`, paper/paper.tex: the literal family
scan has exactly one record per bounded-degree support. -/
theorem formulaCache_length {V : ℕ} (q : ℕ) (F : Formula V) :
    (formulaCache q F).length = (fam V F.degree).length := by
  rw [formulaCache, List.length_map]
  have h := congrArg List.length (famRecs_eq V F.degree)
  simpa only [List.length_map, famRecs_length] using h.symm

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the signed modular cache sum agrees with the full integer coefficient
of every bounded-degree support. -/
theorem formulaCache_coefficient {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V)
    (s : ℕ) (_hs : s < 2 ^ V) (hdegree : (setOf V s).card ≤ F.degree) :
    (((formulaCache q F).foldl (cachedMobStep q V s ((setOf V s).card % 2)) 0 : ℕ) : ℤ) ≡
      coeff F.expand (setOf V s) [ZMOD (q : ℤ)] := by
  refine (cachedMobFold_modEq q V s _ 0 (formulaCache q F)
    (fun e he => (formulaCache_values q hq F e he).le)).trans ?_
  rw [Nat.cast_zero, zero_add, ← sum_termZ F F.degree s hdegree]
  simp only [formulaCache, List.map_map]
  apply listSum_modEq
  intro p hp
  have hmem := famPairs_mem V F.degree p hp
  by_cases hsub : setOf V p.1 ⊆ setOf V s
  · simp only [Function.comp_def, cachedSummand, termZ, hsub, if_true]
    have hv : ((modAlg q p.1).eval F : ℤ) ≡ F.eval (boolPoint (ind (setOf V p.1))) [ZMOD (q : ℤ)] := by
      rw [modAlg_eval q p.1 hq F]
      exact Int.mod_modEq _ _
    by_cases hp' : (setOf V s).card % 2 = p.2 % 2
    · simpa only [hp', if_true, Eq.comm, one_mul] using hv
    · have hp'' : ¬ p.2 % 2 = (setOf V s).card % 2 := Ne.symm hp'
      simpa only [hp', if_false, hp'', neg_one_mul] using hv.neg
  · simp only [Function.comp_def, cachedSummand, termZ, hsub, if_false]
    exact Int.ModEq.refl _

end NearQuarticWires.StageRecovery
