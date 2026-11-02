import Proof.Quartic.StageLift.SourceCarrier
import Proof.Quartic.StageFormulaMetadata.Machine
import Proof.Quartic.StageFormulaMetadata.Cost
import Proof.Quartic.StageFormulaMetadata.ConsumerDock

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print` and `sec:params`, paper/paper.tex: the actual tuple source uses the original selected
quartic degree bound, for every original walk and every raw index. -/
theorem sourceWalkFormula_degree {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    (sourceWalkFormula r index).degree ≤ residueDegreeBound r.child.selected.1 r.prime := by
  unfold sourceWalkFormula
  exact tupleResidueWalkFormula_degree _ _ _ _ _ _ _ _ _

/-- `lem:print`, paper/paper.tex: literal source
bytes, their proved degree and the actual prime-membership guard
supply erased validity for the one shared cold formatter. -/
theorem sourceWalkPacket_valid {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    StageFormulaMetadata.RawWalkPacket.Valid (sourceWalkPacket r index) := by
  refine ⟨sourceWalkFormula r index, rfl, sourceWalkFormula_degree r index, Or.inr ?_⟩
  exact Reconstruct.PrintRequest.two_le_modulus r

/-- `lem:print`, paper/paper.tex: the validity
witness contributes no fields to the actual five-field raw packet. -/
noncomputable def validSourceWalkPacket {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) : StageFormulaMetadata.ValidPacket :=
  ⟨sourceWalkPacket r index, sourceWalkPacket_valid r index⟩

/-- `lem:print`, paper/paper.tex: formatting the
actual source packet yields exactly the unchanged indexed finite-family
compiler request, including the physically computed normalized hint. -/
theorem sourceWalkPacket_formatter_output {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    (validSourceWalkPacket r index).output = natWord index.val ++
      (StageFormulaMetadata.modularFamily (r.prime ^ r.child.selected.1.e)
        (residueDegreeBound r.child.selected.1 r.prime) (sourceWalkFormula r index)
        (Reconstruct.PrintRequest.two_le_modulus r) (sourceWalkFormula_degree r index)).word := by
  exact StageFormulaMetadata.ValidPacket.output_modular (validSourceWalkPacket r index)
    (sourceWalkFormula r index) rfl (sourceWalkFormula_degree r index)
    (Reconstruct.PrintRequest.two_le_modulus r)

/-- `prop:time`, paper/paper.tex: the actual cold
formatter's complete physical cost is charged to the literal packet
length, without a logical Formula-size or hint input premise. -/
theorem sourceWalkPacket_formatter_budget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) :
    (validSourceWalkPacket r index).budget ≤
      10 ^ 15 * ((sourceWalkPacket r index).word.length + 1) ^ 4 := by
  exact StageFormulaMetadata.rawFormatter_budget_le (validSourceWalkPacket r index)

end NearQuarticWires.StageLift
