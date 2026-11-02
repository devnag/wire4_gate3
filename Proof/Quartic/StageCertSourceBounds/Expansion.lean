import Proof.Quartic.StageCertSourceBounds.Source
import Proof.Quartic.Cells.ParametersExpansionCost

set_option autoImplicit false

namespace NearQuarticWires.StageCertSourceBounds

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual exact integer expansion engine has this
fixed original-input-class coefficient after its literal source price
and the fixed eighth and third arity factors are included. -/
noncomputable def actualExpansionCoefficient (B1 B2 : ℕ) : ℕ :=
  10 ^ 11 * (actualFormulaCoefficient B1 B2) ^ 8 * 35 ^ 8 * 36 ^ 3

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual engine's eighth source power and fixed
arity factors contribute this original-arity polynomial exponent. -/
noncomputable def actualExpansionExponent (B1 B2 : ℕ) : ℕ :=
  8 * actualFormulaExponent B1 B2 + 44

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual exact integer expansion machine, applied
to every physically emitted original Formula and summed over the full
closed-walk census, fits the unchanged selected column reserve. The
statement includes all original calls, witnesses and source tests,
without a supplied Formula, source budget or passing-column premise. -/
theorem actualExpansion_all_walks {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    2 ^ (4 * r.selected.1.k) * NearCubicGates.Close.Expand.expansionMachine.budget
      ⟨17 * (Builder.allGates r.call).length, r.formula⟩ ≤
      actualExpansionCoefficient B1 B2 * (r.call.n + 1) ^ actualExpansionExponent B1 B2 *
        2 ^ (r.call.n - r.selected.1.k) := by
  exact r.rules.expansionMachine_all_walks_budget
    (17 * (Builder.allGates r.call).length)
    (16 * r.selected.1.Xmax + 8 * r.selected.1.k) r.selected.1.Xmax
    (actualFormulaCoefficient B1 B2) (actualFormulaExponent B1 B2) r.formula
    r.formula_degree r.source_degree_guard (by omega) (actual_pool_arity_le r)
    r.source_occurrence_guard (actual_formula_source_arity r)

end NearQuarticWires.StageCertSourceBounds
