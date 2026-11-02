import Proof.Quartic.StageLift.MasksContract
import Proof.Quartic.StageLift.SourceCarrier

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the actual
source AST is exactly the original split coefficient times the literal
eight guarded-tuple masks times the original amplified residue body. -/
theorem sourceWalkFormula_shape {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    sourceWalkFormula r index = Formula.mul
      (.const (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ index)))
      (.mul (printMasksFormula r index) (residueBodyFormula r)) := rfl

/-- `lem:print`, paper/paper.tex: composing the
actual three source writers and two multiplication tokens gives the
literal canonical postfix payload, with no Formula input word. -/
theorem sourceWalkFormula_tokens {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    (toks (sourceWalkFormula r index)).flatMap tokWord =
      tokWord (.const (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ index))) ++
      (toks (printMasksFormula r index)).flatMap tokWord ++
      (toks (residueBodyFormula r)).flatMap tokWord ++ tokWord .mul ++ tokWord .mul := by
  rw [sourceWalkFormula_shape]
  simp only [toks, List.flatMap_append, List.flatMap_singleton, List.append_assoc]

end NearQuarticWires.StageLift
