import Proof.Quartic.StageCert.MomentFrontendMachine
import Proof.Quartic.StageFormulaMetadata.ConsumerDock

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats

/-- `prop:time`, paper/paper.tex: the complete
source clock charges the actual structural frontend and actual signed
packet body, including their finite framed stream handoff. -/
noncomputable def MomentRequest.sourceBudget {B1 B2 : ℕ} (r : MomentRequest B1 B2) : ℕ :=
  4*r.frontendBudget+4*r.bodyBudget+12

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed ordinary machine takes ONLY original
prep, actual five-field test metadata and the actual term ordinal,
and prints the exact signed q=0 packet on every proposed witness. -/
noncomputable def momentSourceWordFunction (B1 B2 : ℕ) :
    WordFunction (MomentRequest B1 B2) MomentRequest.word
      (fun r=>frame r.packet.word) MomentRequest.sourceBudget :=
  Program.WordFunction.pipe (momentFrontendWordFunction B1 B2) (momentBodyWordFunction B1 B2)

/-- `lem:print`, paper/paper.tex: the physically
emitted actual Formula has exactly the declared literal moment degree. -/
theorem MomentRequest.formula_degree {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.formula.degree≤r.packet.degree := by
  change r.formula.degree≤16*r.selected.1.Xmax+8*r.selected.1.k
  cases ht : r.test with
  | population =>
    simp only [MomentRequest.formula,ht]
    exact (StagePrint.selectedPopulationMomentFormula_degree (by decide : 0<4) _ _ _ _).trans (by omega)
  | digit j code row =>
    simp only [MomentRequest.formula,ht]
    rw [source_digit_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j row code.val]
    exact tupleCallMomentFormula_degree _ _ _ _ _ _ _
  | finalError j code =>
    simp only [MomentRequest.formula,ht]
    rw [source_final_moment_eq_tuple r.call r.rules r.retainedWitness r.walk j code.val]
    exact tupleCallMomentFormula_degree _ _ _ _ _ _ _

/-- `lem:print`, paper/paper.tex: exact source
validity is an erased proof about the physically emitted bytes and
degree. No Formula, token census or allocator hint is on the input. -/
noncomputable def MomentRequest.validPacket {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    StageFormulaMetadata.ValidPacket :=
  ⟨r.packet,⟨r.formula,rfl,r.formula_degree,Or.inl rfl⟩⟩

/-- `lem:print`, paper/paper.tex: the actual
source Formula itself supplies the exact formatter witness; choice
of an erased validity witness cannot change its signed output bytes. -/
theorem MomentRequest.formatted_exact {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    let hint := StageFormulaMetadata.countedHint r.packet.arity 0 (toks r.formula)
    r.validPacket.output=natWord r.index.val++
      natWord (hint+(r.packet.degree+r.packet.arity+10)^2)++natWord r.packet.degree++
      natWord r.packet.payload.length++natWord hint++natWord 0++
      formulaWord ⟨r.packet.arity,r.formula⟩ :=
  StageFormulaMetadata.ValidPacket.output_exact r.validPacket r.formula rfl rfl

end NearQuarticWires.StageCert.Tokens
