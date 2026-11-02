import Proof.Quartic.StageRecovery.ModTerms

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: modular normalization
retains only monomials already present in its input stream. -/
theorem normalizeMod_keys {V : ℕ} (modulus : ℕ) (terms : Terms V) :
    ∀ S ∈ Terms.keys (normalizeMod modulus terms), S ∈ Terms.keys terms := by
  intro S hS
  rw [normalizeMod, reduceTerms_keys] at hS
  have h := Terms.keys_normalize _ S hS
  rwa [reduceTerms_keys] at h

/-- `lem:print`, paper/paper.tex: modular normalization
merges equal supports and leaves no duplicate monomials. -/
theorem normalizeMod_nodup {V : ℕ} (modulus : ℕ) (terms : Terms V) :
    (Terms.keys (normalizeMod modulus terms)).Nodup := by
  rw [normalizeMod, reduceTerms_keys]
  exact Terms.nodup_normalize _

/-- `lem:print`, paper/paper.tex: a modular term power
uses at most the power times the original formal degree. -/
theorem powerMod_card {V : ℕ} (modulus : ℕ) (terms : Terms V) (D : ℕ)
    (hterms : ∀ S ∈ Terms.keys terms, S.card ≤ D) (exponent : ℕ) :
    ∀ S ∈ Terms.keys (powerMod modulus terms exponent), S.card ≤ exponent * D := by
  induction exponent with
  | zero => simp [powerMod, reduceTerms_keys, Terms.one]
  | succ exponent ih =>
      intro S hS
      obtain ⟨A, hA, B, hB, rfl⟩ := Terms.keys_rawMul _ _ S
        (normalizeMod_keys modulus _ S hS)
      exact (Finset.card_union_le A B).trans
        (by have := ih A hA; have := hterms B hB; nlinarith)

/-- `lem:print`, paper/paper.tex: reduction between
formula operations preserves the full formal degree bound. -/
theorem expandMod_card {V : ℕ} (modulus : ℕ) (formula : Formula V) :
    ∀ S ∈ Terms.keys (expandMod modulus formula), S.card ≤ formula.degree := by
  induction formula with
  | const value => simp [expandMod, reduceTerms_keys, Formula.degree]
  | var atom => simp [expandMod, reduceTerms_keys, Formula.degree]
  | add left right ihl ihr =>
      intro S hS
      have h := normalizeMod_keys modulus _ S hS
      rw [Terms.keys_append, List.mem_append] at h
      rcases h with h | h
      · exact (ihl S h).trans (le_max_left _ _)
      · exact (ihr S h).trans (le_max_right _ _)
  | neg child ih =>
      intro S hS
      rw [expandMod, reduceTerms_keys, Terms.keys_neg] at hS
      exact ih S hS
  | sub left right ihl ihr =>
      intro S hS
      have h := normalizeMod_keys modulus _ S hS
      rw [Terms.keys_append, Terms.keys_neg, List.mem_append] at h
      rcases h with h | h
      · exact (ihl S h).trans (le_max_left _ _)
      · exact (ihr S h).trans (le_max_right _ _)
  | mul left right ihl ihr =>
      intro S hS
      obtain ⟨A, hA, B, hB, rfl⟩ := Terms.keys_rawMul _ _ S
        (normalizeMod_keys modulus _ S hS)
      exact (Finset.card_union_le A B).trans (Nat.add_le_add (ihl A hA) (ihr B hB))
  | pow child exponent ih => exact powerMod_card modulus _ _ ih exponent

/-- `lem:print`, paper/paper.tex: every modular power
has a duplicate-free dense support list. -/
theorem powerMod_nodup {V : ℕ} (modulus : ℕ) (terms : Terms V) (exponent : ℕ) :
    (Terms.keys (powerMod modulus terms exponent)).Nodup := by
  cases exponent with
  | zero => simp [powerMod, reduceTerms_keys, Terms.one]
  | succ exponent => exact normalizeMod_nodup modulus _

/-- `lem:print`, paper/paper.tex: the modular expansion
retains the same dense monomial census bound as exact expansion. -/
theorem expandMod_nodup {V : ℕ} (modulus : ℕ) (formula : Formula V) :
    (Terms.keys (expandMod modulus formula)).Nodup := by
  induction formula with
  | const value => simp [expandMod, reduceTerms_keys]
  | var atom => simp [expandMod, reduceTerms_keys]
  | add left right _ _ => exact normalizeMod_nodup modulus _
  | neg child ih => simpa only [expandMod, reduceTerms_keys, Terms.keys_neg] using ih
  | sub left right _ _ => exact normalizeMod_nodup modulus _
  | mul left right _ _ => exact normalizeMod_nodup modulus _
  | pow child exponent _ => exact powerMod_nodup modulus _ exponent

/-- `lem:print`, paper/paper.tex: coefficient reduction
does not worsen the actual dense term-count envelope. -/
theorem expandMod_length {V : ℕ} (modulus : ℕ) (formula : Formula V) :
    (expandMod modulus formula).length ≤
      ∑ d ∈ Finset.range (formula.degree + 1), V.choose d :=
  Terms.length_le formula.degree _ (expandMod_nodup modulus formula) (expandMod_card modulus formula)

end NearQuarticWires.StageRecovery
