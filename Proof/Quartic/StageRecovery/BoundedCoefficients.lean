import Proof.Quartic.StageRecovery.CacheBuild

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the physical cache
uses the serialized degree upper bound, without computing the exact
degree of the original Formula. -/
def boundedFormulaCache {V : ℕ} (q : ℕ) (F : Formula V) (D : ℕ) : List CachedValue :=
  pointEntries q F (famPairs V D)

/-- `lem:print`, paper/paper.tex: every generated
support has one actually evaluated, reduced cache value. -/
theorem boundedFormulaCache_values {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V) (D : ℕ) :
    ∀ e ∈ boundedFormulaCache q F D, e.2.2 < q := by
  intro e he
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp he
  exact (modAlg q p.1).eval_lt (modAlg_closed q p.1 hq) F

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the actual finite scan recovers each coefficient modulo the given
positive modulus for every serialized degree upper bound. -/
theorem boundedFormulaCache_coefficient {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V)
    (D s : ℕ) (hdegree : (setOf V s).card ≤ D) :
    (((boundedFormulaCache q F D).foldl (cachedMobStep q V s ((setOf V s).card % 2)) 0 : ℕ) : ℤ) ≡
      coeff F.expand (setOf V s) [ZMOD (q : ℤ)] := by
  refine (cachedMobFold_modEq q V s _ 0 (boundedFormulaCache q F D)
    (fun e he => (boundedFormulaCache_values q hq F D e he).le)).trans ?_
  rw [Nat.cast_zero, zero_add, ← sum_termZ F D s hdegree]
  simp only [boundedFormulaCache, pointEntries, List.map_map]
  apply listSum_modEq
  intro p hp
  by_cases hsub : setOf V p.1 ⊆ setOf V s
  · simp only [Function.comp_def, cachedSummand, termZ, hsub, if_true]
    have hv : ((modAlg q p.1).eval F : ℤ) ≡
        F.eval (boolPoint (ind (setOf V p.1))) [ZMOD (q : ℤ)] := by
      rw [modAlg_eval q p.1 hq F]
      exact Int.mod_modEq _ _
    by_cases hp' : (setOf V s).card % 2 = p.2 % 2
    · simpa only [hp', if_true, Eq.comm, one_mul] using hv
    · have hp'' : ¬ p.2 % 2 = (setOf V s).card % 2 := Ne.symm hp'
      simpa only [hp', if_false, hp'', neg_one_mul] using hv.neg
  · simp only [Function.comp_def, cachedSummand, termZ, hsub, if_false]
    exact Int.ModEq.refl _

/-- `lem:print`, paper/paper.tex: the canonical dense
Terms retain zero coefficients and follow exactly the bounded family. -/
def boundedModTerms {V : ℕ} (q : ℕ) (F : Formula V) (D : ℕ) : Terms V :=
  (famS V D).map fun S => (S, coeff F.expand S % (q : ℤ))

/-- `lem:print`, paper/paper.tex: the complete bounded
term stream has the literal native support census, with no sparse oracle. -/
theorem boundedModTerms_length {V : ℕ} (q : ℕ) (F : Formula V) (D : ℕ) :
    (boundedModTerms q F D).length ≤ (V + 1) ^ D := by
  simpa only [boundedModTerms, famS, List.length_map] using fam_length_le V D

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the full bounded term list equals the original Formula on every Boolean
assignment modulo the actual modulus, including prime powers. -/
theorem boundedModTerms_eval {V : ℕ} (q : ℕ) (F : Formula V) (D : ℕ)
    (hD : F.degree ≤ D) (b : Fin V → Bool) :
    Terms.eval b (boundedModTerms q F D) ≡ F.eval (boolPoint b) [ZMOD (q : ℤ)] := by
  have hkeys : ∀ S ∈ Terms.keys F.expand, S ∈ famS V D :=
    fun S hS => fam_complete V D S ((Formula.expand_card_le F S hS).trans hD)
  rw [← Formula.expand_eval, ← sum_coeff_eval F.expand (famS V D) (famS_nodup V D) hkeys b]
  simp only [Terms.eval, boundedModTerms, List.map_map, Function.comp_def]
  apply listSum_modEq
  intro S _
  exact (Int.mod_modEq _ _).mul (Int.ModEq.refl _)

/-- `lem:print`, paper/paper.tex: every output coefficient
has the canonical nonnegative residue representation before serialization. -/
theorem boundedModTerms_bounds {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V) (D : ℕ) :
    ∀ term ∈ boundedModTerms q F D, 0 ≤ term.2 ∧ term.2 < (q : ℤ) := by
  intro term ht
  obtain ⟨S, _, rfl⟩ := List.mem_map.mp ht
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  exact ⟨Int.emod_nonneg _ (ne_of_gt hqz), Int.emod_lt_of_pos _ hqz⟩

end NearQuarticWires.StageRecovery
