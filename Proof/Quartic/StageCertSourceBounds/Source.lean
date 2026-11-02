import Proof.Quartic.StageCert.MomentSyntaxScale
import Proof.Quartic.StageCert.MomentRuntimeArity
import Proof.Quartic.StageCert.MomentSourcePrice

set_option autoImplicit false

namespace NearQuarticWires.StageCertSourceBounds

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed coefficient prices the literal actual signed
Formula codec, syntax and construction weight for the original input class. -/
noncomputable def actualFormulaCoefficient (B1 B2 : ℕ) : ℕ :=
  100000 * (momentRuntimeCoefficient B1 B2) ^ 4

/-- `lem:print` and `prop:time`, paper/paper.tex: the fourth power of the actual source runtime scale
contributes this fixed original-arity exponent. -/
noncomputable def actualFormulaExponent (B1 B2 : ℕ) : ℕ :=
  4 * momentRuntimeExponent B1 B2

/-- `prop:time`, paper/paper.tex: the fourth
source-scale power is separated into its fixed arity coefficient and
exponent without changing the literal signed-source tuple factor. -/
private theorem source_scale_rearrange (C n e P : ℕ) :
    100000 * (C * (n + 1) ^ e) ^ 4 * P =
      (100000 * C ^ 4) * (n + 1) ^ (4 * e) * P := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm e 4]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: for every actual population, digit or final-error
request, its complete literal signed Formula source, syntax and weight
have one fixed original-arity price with the displayed occurrence factor.
All original witnesses and uncertified columns are included. -/
theorem actual_formula_source_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (formulaWord ⟨17 * (Builder.allGates r.call).length, r.formula⟩).length +
      r.formula.size + r.formula.weight + 1 ≤
      actualFormulaCoefficient B1 B2 * (r.call.n + 1) ^ actualFormulaExponent B1 B2 *
        (17 * (Builder.allGates r.call).length + 1) ^ (r.selected.1.Xmax + 1) := by
  let G := (Builder.allGates r.call).length
  have hp := Nat.pow_le_pow_left r.runtimeScale_arity 4
  have htuple : (G + 1) ^ r.selected.1.Xmax ≤
      (17 * G + 1) ^ (r.selected.1.Xmax + 1) :=
    (Nat.pow_le_pow_left (by omega : G + 1 ≤ 17 * G + 1) _).trans
      (Nat.pow_le_pow_right (by omega : 0 < 17 * G + 1) (by omega))
  calc
    _ ≤ 100000 * r.runtimeScale ^ 4 * (G + 1) ^ r.selected.1.Xmax :=
      r.raw_formula_source_scale
    _ ≤ 100000 * (momentRuntimeCoefficient B1 B2 *
        (r.call.n + 1) ^ momentRuntimeExponent B1 B2) ^ 4 * (G + 1) ^ r.selected.1.Xmax :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = actualFormulaCoefficient B1 B2 * (r.call.n + 1) ^ actualFormulaExponent B1 B2 *
        (G + 1) ^ r.selected.1.Xmax := source_scale_rearrange _ _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ htuple

/-- `sec:params` and `lem:print`, paper/paper.tex: both complete original occurrence lists satisfy the
actual selected quartic census before any source test or column passes. -/
theorem actual_gate_count_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    (Builder.allGates r.call).length ≤ 2 * r.call.n ^ 4 := by
  have hh := r.rules.input_valid.2.2.1.trans r.rules.input_valid.2.2.2.1
  simpa only [Builder.callInput, Builder.allGates, List.length_append] using hh

/-- `sec:params` and `lem:print`, paper/paper.tex: the actual seventeen-role original occurrence pool
has the concrete quartic arity required by exact integer expansion. -/
theorem actual_pool_arity_le {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    17 * (Builder.allGates r.call).length ≤ 34 * r.call.n ^ 4 := by
  have h := Nat.mul_le_mul_left 17 (actual_gate_count_le r)
  exact h.trans_eq (by ring)

end NearQuarticWires.StageCertSourceBounds
