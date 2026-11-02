import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print` and `lem:residue`, paper/paper.tex: coefficient tokens are normalized before the formula
enters modular coefficient expansion. -/
def reduceConstants {V : ℕ} (q : ℕ) : Formula V → Formula V
  | .const z => .const (z % (q : ℤ))
  | .var v => .var v
  | .add f g => .add (reduceConstants q f) (reduceConstants q g)
  | .neg f => .neg (reduceConstants q f)
  | .sub f g => .sub (reduceConstants q f) (reduceConstants q g)
  | .mul f g => .mul (reduceConstants q f) (reduceConstants q g)
  | .pow f e => .pow (reduceConstants q f) e

/-- `lem:print` and `lem:residue`, paper/paper.tex: reducing the generated constant leaves preserves the
literal formula's value modulo the actual prime power. -/
theorem reduceConstants_eval {V : ℕ} (q : ℕ) (F : Formula V) (β : Fin V → ℤ) :
    (reduceConstants q F).eval β ≡ F.eval β [ZMOD (q : ℤ)] := by
  induction F with
  | const z => exact Int.mod_modEq z q
  | var v => exact Int.ModEq.refl _
  | add f g hf hg => exact hf.add hg
  | neg f hf => exact hf.neg
  | sub f g hf hg => exact hf.sub hg
  | mul f g hf hg => exact hf.mul hg
  | pow f e hf => exact hf.pow e

/-- `lem:print`, paper/paper.tex: coefficient
normalization does not enlarge the formal degree used in the quartic
monomial census. -/
theorem reduceConstants_degree {V : ℕ} (q : ℕ) (F : Formula V) :
    (reduceConstants q F).degree = F.degree := by
  induction F <;> simp_all [reduceConstants, Formula.degree]

/-- `lem:print`, paper/paper.tex: reducing constants
retains the exact syntactic size, including original exponent counts. -/
theorem reduceConstants_size {V : ℕ} (q : ℕ) (F : Formula V) :
    (reduceConstants q F).size = F.size := by
  induction F <;> simp_all [reduceConstants, Formula.size]

/-- `lem:print`, paper/paper.tex: modular coefficient
normalization changes no postfix token count or operation order. -/
theorem reduceConstants_token_count {V : ℕ} (q : ℕ) (F : Formula V) :
    (toks (reduceConstants q F)).length = (toks F).length := by
  induction F <;> simp_all [reduceConstants, toks]

/-- `lem:print`, paper/paper.tex: every emitted
constant token is nonnegative and strictly below the recovery modulus. -/
theorem reduceConstants_token_bound {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V)
    (z : ℤ) (hz : Tok.const z ∈ toks (reduceConstants q F)) : 0 ≤ z ∧ z < q := by
  induction F with
  | const a =>
      simp only [reduceConstants, toks, List.mem_singleton, Tok.const.injEq] at hz
      subst z
      exact ⟨Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt hq)),
        Int.emod_lt_of_pos _ (by exact_mod_cast hq)⟩
  | var v => simp [reduceConstants, toks] at hz
  | add f g hf hg =>
      simp only [reduceConstants, toks, List.mem_append, List.mem_singleton] at hz
      rcases hz with (h | h) | h
      · exact hf h
      · exact hg h
      · cases h
  | neg f hf =>
      simp only [reduceConstants, toks, List.mem_append, List.mem_singleton] at hz
      rcases hz with h | h
      · exact hf h
      · cases h
  | sub f g hf hg =>
      simp only [reduceConstants, toks, List.mem_append, List.mem_singleton] at hz
      rcases hz with (h | h) | h
      · exact hf h
      · exact hg h
      · cases h
  | mul f g hf hg =>
      simp only [reduceConstants, toks, List.mem_append, List.mem_singleton] at hz
      rcases hz with (h | h) | h
      · exact hf h
      · exact hg h
      · cases h
  | pow f e hf =>
      simp only [reduceConstants, toks, List.mem_append, List.mem_singleton] at hz
      rcases hz with h | h
      · exact hf h
      · cases h

end NearQuarticWires.StageLift
