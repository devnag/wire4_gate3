import Proof.Quartic.StageRecovery.ModPointCost

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Tabulator NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: summing congruent
literal integer records preserves their exact recovery residue. -/
theorem listSum_modEq {α : Type*} (q : ℤ) (xs : List α) (f g : α → ℤ)
    (h : ∀ x ∈ xs, f x ≡ g x [ZMOD q]) :
    (xs.map f).sum ≡ (xs.map g).sum [ZMOD q] := by
  induction xs with
  | nil => exact Int.ModEq.refl 0
  | cons x xs ih =>
      exact (h x (by simp)).add (ih (fun y hy => h y (by simp [hy])))

/-- `lem:print`, paper/paper.tex: one dense coefficient
is the finite integer Möbius sum of bounded formula point residues.
Every summand uses an actually evaluated characteristic point. -/
def denseCoefficient {V : ℕ} (q : ℕ) (formula : Formula V) (S : Finset (Fin V)) : ℤ :=
  (((fam V formula.degree).map fun point =>
    if setOf V point ⊆ S then
      (-1 : ℤ) ^ (S \ setOf V point).card * ((modAlg q point).eval formula : ℤ)
    else 0).sum) % (q : ℤ)

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
integer Möbius inversion recovers each coefficient modulo the actual
positive modulus, including composite prime powers, without division. -/
theorem denseCoefficient_eq {V : ℕ} (q : ℕ) (hq : 0 < q) (formula : Formula V)
    (S : Finset (Fin V)) (hS : S.card ≤ formula.degree) :
    denseCoefficient q formula S = coeff formula.expand S % (q : ℤ) := by
  rw [coeff_eq_fam formula formula.degree S hS]
  unfold denseCoefficient famS
  rw [List.map_map]
  apply listSum_modEq
  intro point _
  by_cases hs : setOf V point ⊆ S
  · simp only [Function.comp_def, hs, if_true]
    have hv : ((modAlg q point).eval formula : ℤ) ≡
        formula.eval (boolPoint (ind (setOf V point))) [ZMOD (q : ℤ)] := by
      rw [modAlg_eval q point hq formula]
      exact Int.mod_modEq _ _
    exact (Int.ModEq.refl _).mul hv
  · simp only [Function.comp_def, hs, if_false]
    exact Int.ModEq.refl _

/-- `lem:print`, paper/paper.tex: the deterministic
dense modular term stream uses each bounded-degree support once,
retaining zero coefficients rather than introducing a sparse oracle. -/
def denseModTerms {V : ℕ} (q : ℕ) (formula : Formula V) : Terms V :=
  (famS V formula.degree).map fun S => (S, denseCoefficient q formula S)

/-- `lem:print`, paper/paper.tex: the actual dense
support order is precisely the original finite family order. -/
theorem denseModTerms_keys {V : ℕ} (q : ℕ) (formula : Formula V) :
    Terms.keys (denseModTerms q formula) = famS V formula.degree := by
  simp [denseModTerms, Terms.keys, List.map_map, Function.comp_def]

/-- `lem:print`, paper/paper.tex: the dense modular
compiler retains unique supports and the exact formal degree bound. -/
theorem denseModTerms_support {V : ℕ} (q : ℕ) (formula : Formula V) :
    (Terms.keys (denseModTerms q formula)).Nodup ∧
      ∀ S ∈ Terms.keys (denseModTerms q formula), S.card ≤ formula.degree := by
  rw [denseModTerms_keys]
  exact ⟨famS_nodup _ _, famS_card _ _⟩

/-- `lem:print`, paper/paper.tex: the exact dense
coefficient census is at most `(V+1)^D`, so a pair of sequential
family scans has the literal exponent `2D`. -/
theorem denseModTerms_length {V : ℕ} (q : ℕ) (formula : Formula V) :
    (denseModTerms q formula).length ≤ (V + 1) ^ formula.degree := by
  simpa only [denseModTerms, famS, List.length_map] using fam_length_le V formula.degree

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the complete dense term list evaluates to the original Boolean formula
modulo the actual recovery modulus, with no inverse assumptions. -/
theorem denseModTerms_eval {V : ℕ} (q : ℕ) (hq : 0 < q) (formula : Formula V)
    (b : Fin V → Bool) :
    Terms.eval b (denseModTerms q formula) ≡ formula.eval (boolPoint b) [ZMOD (q : ℤ)] := by
  have hkeys : ∀ S ∈ Terms.keys formula.expand, S ∈ famS V formula.degree :=
    fun S hS => fam_complete V formula.degree S (Formula.expand_card_le formula S hS)
  rw [← Formula.expand_eval, ← sum_coeff_eval formula.expand (famS V formula.degree)
    (famS_nodup V formula.degree) hkeys b]
  simp only [Terms.eval, denseModTerms, List.map_map, Function.comp_def]
  apply listSum_modEq
  intro S hS
  rw [denseCoefficient_eq q hq formula S (famS_card V formula.degree S hS)]
  exact (Int.mod_modEq _ _).mul (Int.ModEq.refl _)

/-- `lem:print`, paper/paper.tex: each dense output
coefficient lies in the actual finite residue interval before it is
copied to the native weighted-cut bank. -/
theorem denseModTerms_bounds {V : ℕ} (q : ℕ) (hq : 0 < q) (formula : Formula V) :
    ∀ term ∈ denseModTerms q formula, 0 ≤ term.2 ∧ term.2 < (q : ℤ) := by
  intro term ht
  obtain ⟨S, _, rfl⟩ := List.mem_map.mp ht
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  exact ⟨Int.emod_nonneg _ (ne_of_gt hqz), Int.emod_lt_of_pos _ hqz⟩

end NearQuarticWires.StageRecovery
