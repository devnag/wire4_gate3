import Proof.Gates.Tabulator.Formula
import Proof.Quartic.StageRecovery.Coefficients

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: reduce every emitted
monomial coefficient before it is passed to the original cut compiler. -/
def reduceTerms {V : ℕ} (modulus : ℕ) (terms : Terms V) : Terms V :=
  terms.map fun term => (term.1, term.2 % (modulus : ℤ))

/-- `lem:print`, paper/paper.tex: coefficient reduction
preserves the ordered monomial supports and their exact census. -/
theorem reduceTerms_keys {V : ℕ} (modulus : ℕ) (terms : Terms V) :
    Terms.keys (reduceTerms modulus terms) = Terms.keys terms := by
  simp [reduceTerms, Terms.keys, List.map_map, Function.comp_def]

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the reduced term stream evaluates to the same residue at every actual
Boolean assignment of the original atom pool. -/
theorem reduceTerms_eval {V : ℕ} (modulus : ℕ) (terms : Terms V) (b : Fin V → Bool) :
    Terms.eval b (reduceTerms modulus terms) ≡ Terms.eval b terms [ZMOD (modulus : ℤ)] := by
  induction terms with
  | nil => exact Int.ModEq.refl _
  | cons term terms ih =>
      change ((term.2 % (modulus : ℤ)) * monomialValue b term.1 +
        Terms.eval b (reduceTerms modulus terms)) ≡
          term.2 * monomialValue b term.1 + Terms.eval b terms [ZMOD (modulus : ℤ)]
      exact ((Int.mod_modEq term.2 (modulus : ℤ)).mul (Int.ModEq.refl _)).add ih

/-- `lem:print`, paper/paper.tex: every retained reduced
term coefficient is nonnegative and strictly below the modulus. -/
theorem reduceTerms_bounds {V : ℕ} (modulus : ℕ) (hm : 0 < modulus)
    (terms : Terms V) : ∀ term ∈ reduceTerms modulus terms,
      0 ≤ term.2 ∧ term.2.natAbs < modulus := by
  intro term ht
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp ht
  exact ⟨Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hm)),
    reduceCut_bound modulus hm ⟨[], [], 0, original.2⟩⟩

/-- `lem:print`, paper/paper.tex: normalize a finite
stream of reduced terms and reduce the merged coefficients again. -/
def normalizeMod {V : ℕ} (modulus : ℕ) (terms : Terms V) : Terms V :=
  reduceTerms modulus (Terms.normalize (reduceTerms modulus terms))

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the merged reduced stream preserves the exact residue polynomial. -/
theorem normalizeMod_eval {V : ℕ} (modulus : ℕ) (terms : Terms V) (b : Fin V → Bool) :
    Terms.eval b (normalizeMod modulus terms) ≡ Terms.eval b terms [ZMOD (modulus : ℤ)] := by
  have h := reduceTerms_eval modulus (Terms.normalize (reduceTerms modulus terms)) b
  rw [Terms.eval_normalize] at h
  exact h.trans (reduceTerms_eval modulus terms b)

/-- `lem:print`, paper/paper.tex: multiply reduced term
streams with coefficients reduced before the next formula operation. -/
def multiplyMod {V : ℕ} (modulus : ℕ) (left right : Terms V) : Terms V :=
  normalizeMod modulus (Terms.rawMul left right)

/-- `lem:print`, paper/paper.tex: iterated powers reduce
the coefficients after each multiplication. -/
def powerMod {V : ℕ} (modulus : ℕ) (terms : Terms V) : ℕ → Terms V
  | 0 => reduceTerms modulus Terms.one
  | exponent + 1 => multiplyMod modulus (powerMod modulus terms exponent) terms

/-- `lem:residue`, paper/paper.tex: modular term powers
agree with the exact integer power at every Boolean atom assignment. -/
theorem powerMod_eval {V : ℕ} (modulus : ℕ) (terms : Terms V)
    (exponent : ℕ) (b : Fin V → Bool) :
    Terms.eval b (powerMod modulus terms exponent) ≡ (Terms.eval b terms) ^ exponent
      [ZMOD (modulus : ℤ)] := by
  induction exponent with
  | zero => simpa [powerMod, Terms.eval_one] using reduceTerms_eval modulus (Terms.one : Terms V) b
  | succ exponent ih =>
      have h := normalizeMod_eval modulus (Terms.rawMul (powerMod modulus terms exponent) terms) b
      rw [Terms.eval_rawMul] at h
      exact h.trans (by simpa [pow_succ] using ih.mul (Int.ModEq.refl (Terms.eval b terms)))

/-- `lem:print`, paper/paper.tex: a concrete modular
formula expansion retains the original Boolean variables and reduces
coefficient arithmetic between formula operations. -/
def expandMod {V : ℕ} (modulus : ℕ) : Formula V → Terms V
  | .const value => reduceTerms modulus [(∅, value)]
  | .var atom => reduceTerms modulus [({atom}, 1)]
  | .add left right => normalizeMod modulus (expandMod modulus left ++ expandMod modulus right)
  | .neg child => reduceTerms modulus (Terms.neg (expandMod modulus child))
  | .sub left right => normalizeMod modulus (expandMod modulus left ++ Terms.neg (expandMod modulus right))
  | .mul left right => multiplyMod modulus (expandMod modulus left) (expandMod modulus right)
  | .pow child exponent => powerMod modulus (expandMod modulus child) exponent

/-- `lem:residue`, paper/paper.tex, and `lem:print`:1573–1585:
the concrete coefficient-reduced expansion represents exactly the
amplified residue formula modulo the recovery modulus. -/
theorem expandMod_eval {V : ℕ} (modulus : ℕ) (formula : Formula V) (b : Fin V → Bool) :
    Terms.eval b (expandMod modulus formula) ≡ formula.eval (boolPoint b)
      [ZMOD (modulus : ℤ)] := by
  induction formula with
  | const value =>
      simpa [expandMod, Terms.eval, monomialValue, Formula.eval] using
        reduceTerms_eval modulus ([(∅, value)] : Terms V) b
  | var atom =>
      simpa [expandMod, Terms.eval, monomialValue, Formula.eval, boolPoint] using
        reduceTerms_eval modulus ([({atom}, 1)] : Terms V) b
  | add left right ihl ihr =>
      have h := normalizeMod_eval modulus (expandMod modulus left ++ expandMod modulus right) b
      rw [Terms.eval_append] at h
      exact h.trans (ihl.add ihr)
  | neg child ih =>
      have h := reduceTerms_eval modulus (Terms.neg (expandMod modulus child)) b
      rw [Terms.eval_neg] at h
      exact h.trans ih.neg
  | sub left right ihl ihr =>
      have h := normalizeMod_eval modulus (expandMod modulus left ++ Terms.neg (expandMod modulus right)) b
      rw [Terms.eval_append, Terms.eval_neg] at h
      exact h.trans (by simpa [Formula.eval, sub_eq_add_neg] using ihl.add ihr.neg)
  | mul left right ihl ihr =>
      have h := normalizeMod_eval modulus (Terms.rawMul (expandMod modulus left) (expandMod modulus right)) b
      rw [Terms.eval_rawMul] at h
      exact h.trans (ihl.mul ihr)
  | pow child exponent ih =>
      exact (powerMod_eval modulus (expandMod modulus child) exponent b).trans (ih.pow exponent)

end NearQuarticWires.StageRecovery
