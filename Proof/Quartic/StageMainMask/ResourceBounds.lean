import Proof.Quartic.StageMainMask.Resources

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open StageMain

/-- `prop:time`, paper/paper.tex: the complete
actual Entry resource allowance includes all source-field widths and
the fixed constants of the native arithmetic and source parsers. -/
theorem entryResources_scale {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    entrySourceScale r + 64 ≤ entryResources r := by
  have hp : entrySourceScale r + 1 ≤ (entrySourceScale r + 1) ^ 4 :=
    Nat.le_self_pow (by decide) _
  have h0 : 1 ≤ (entrySourceScale r + 1) ^ 4 := Nat.pow_pos (Nat.succ_pos _)
  unfold entryResources
  omega

/-- `prop:time`, paper/paper.tex: the actual
nested ordinary selectors, complete cold helper clocks and literal
input and answer copy costs fit the original Entry resource allowance. -/
theorem entryResources_calls {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryCallee B1 B2).bud (.inl (entryStructuralRequest r)) ≤ entryResources r ∧
    (entryCallee B1 B2).bud (.inr (.inl (entryPopulationRequest r))) ≤ entryResources r ∧
    (entryCallee B1 B2).bud (.inr (.inr (entryPredicateRequest r))) ≤ entryResources r := by
  let S := entrySourceScale r
  have hword := entryRequest_words r
  have hsw : (structuralWord (entryStructuralRequest r)).length ≤ S := hword.1
  have hpw : (entryPopulationRequest r).word.length ≤ S := hword.2.1
  have hvw : (entryPredicateRequest r).word.length ≤ S := hword.2.2
  have hS : 1 ≤ S := (entrySourceScale_bounds r).1
  have hpop : (natWord (entryPopulationRequest r).value).length ≤ 2 * S + 1 := by
    have h := entryPopulation_bits r
    have hnb : natBitLength (entryPopulationRequest r).value ≤ S := by
      dsimp only [S, entrySourceScale]
      omega
    rw [NearCubicGates.Close.Dispatch.natWord_length]
    omega
  have hbase : 1000000 * (structuralBudget (entryStructuralRequest r) +
      StageMainPopulation.populationBudget (entryPopulationRequest r) +
      framedPredicateBudget (entryPredicateRequest r).word.length + S + 1) ≤ entryResources r := by
    unfold entryResources
    dsimp only [S]
    omega
  have hs : (entryCallee B1 B2).bud (.inl (entryStructuralRequest r)) ≤
      1000000 * (structuralBudget (entryStructuralRequest r) +
        StageMainPopulation.populationBudget (entryPopulationRequest r) +
        framedPredicateBudget (entryPredicateRequest r).word.length + S + 1) := by
    change 200 * ((structuralWord (entryStructuralRequest r)).length + 1 +
      structuralBudget (entryStructuralRequest r) + 1) + 12 ≤ _
    omega
  have hp : (entryCallee B1 B2).bud (.inr (.inl (entryPopulationRequest r))) ≤
      1000000 * (structuralBudget (entryStructuralRequest r) +
        StageMainPopulation.populationBudget (entryPopulationRequest r) +
        framedPredicateBudget (entryPredicateRequest r).word.length + S + 1) := by
    change 200 * (((false :: (entryPopulationRequest r).word).length) +
      (natWord (entryPopulationRequest r).value).length +
      (200 * ((entryPopulationRequest r).word.length + (natWord (entryPopulationRequest r).value).length +
        StageMainPopulation.populationBudget (entryPopulationRequest r) + 1) + 12) + 1) + 12 ≤ _
    simp only [List.length_cons]
    omega
  have hv : (entryCallee B1 B2).bud (.inr (.inr (entryPredicateRequest r))) ≤
      1000000 * (structuralBudget (entryStructuralRequest r) +
        StageMainPopulation.populationBudget (entryPopulationRequest r) +
        framedPredicateBudget (entryPredicateRequest r).word.length + S + 1) := by
    change 200 * (((true :: (entryPredicateRequest r).word).length) + 1 +
      (200 * ((entryPredicateRequest r).word.length + 1 +
        framedPredicateBudget (entryPredicateRequest r).word.length + 1) + 12) + 1) + 12 ≤ _
    simp only [List.length_cons]
    omega
  exact ⟨hs.trans hbase, hp.trans hbase, hv.trans hbase⟩

/-- `prop:time`, paper/paper.tex: exact original
source and four-point work and all finite reply work are funded by the
same original-arity resource allowance before ordinary call overhead. -/
theorem entryResources_native {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    entryPointCoreSteps r ≤ entryResources r ∧
      evaluationSteps r 0 0 ≤ entryResources r := by
  have hp := entryPointCoreSteps_le r
  have he := evaluationSteps_source_le r
  have hmono : (entrySourceScale r) ^ 4 ≤ (entrySourceScale r + 1) ^ 4 :=
    Nat.pow_le_pow_left (Nat.le_succ _) 4
  have hfirst : 100000000 * (entrySourceScale r + 1) ^ 4 ≤ entryResources r := by
    unfold entryResources
    omega
  have hsecond : 10000 * entrySourceScale r ≤ entryResources r := by
    unfold entryResources
    omega
  exact ⟨hp.trans ((Nat.mul_le_mul (by decide) hmono).trans hfirst), he.trans hsecond⟩

end NearQuarticWires.StageMainMask
