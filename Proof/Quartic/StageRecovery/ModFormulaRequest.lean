import Proof.Quartic.StageRecovery.ModCensus
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: a literal modular
formula and a finite binary-workspace hint, rather than an unreduced
polynomial value or an externally supplied term expansion. -/
structure ModFormulaRequest where
  arity : ℕ
  formula : Formula arity
  modulus : ℕ
  hint : ℕ
  modulus_ge_two : 2 ≤ modulus
  hint_sufficient :
    (arity + formula.size + (formulaWord ⟨arity, formula⟩).length +
      natBitLength modulus + 10) ^ 2 ≤ hint

/-- `lem:print`, paper/paper.tex: the literal physical
input for coefficient compilation has a workspace hint, actual modulus
and the unchanged original postfix formula codec. -/
def ModFormulaRequest.word (r : ModFormulaRequest) : List Bool :=
  natWord r.hint ++ natWord r.modulus ++ formulaWord ⟨r.arity, r.formula⟩

end NearQuarticWires.StageRecovery
