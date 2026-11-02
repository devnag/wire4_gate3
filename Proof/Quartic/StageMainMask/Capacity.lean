import Proof.Quartic.StageMainMask.ResourceBounds

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageMain StageMain.Compact

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the original finite Entry resource
funds every actual scalar width and all three real cold call inputs
and clocks, without an independent source or helper provider premise. -/
theorem entryCallCapacity_of_resources {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (W L B : ℕ) (hW : entryResources r ≤ W) (hL : entryResources r ≤ L)
    (hB : entryResources r ≤ B) : EntryCallCapacity r W L B := by
  let S := entrySourceScale r
  have hscale : S + 64 ≤ entryResources r := entryResources_scale r
  have hs := entrySourceScale_bounds r
  have hsrc := entrySource_lengths r
  have hword := entryRequest_words r
  have hsw : (structuralWord (entryStructuralRequest r)).length ≤ S := hword.1
  have hpw : (entryPopulationRequest r).word.length ≤ S := hword.2.1
  have hvw : (entryPredicateRequest r).word.length ≤ S := hword.2.2
  have hcalls := entryResources_calls r
  have hu := structural_index_bits (entryStructuralRequest r)
  change natBitLength (entryPosition r).1.val ≤ (Program.prepWord B1 B2 r.call r.witness).length ∧
    natBitLength (entryPosition r).2.val ≤ (Program.prepWord B1 B2 r.call r.witness).length at hu
  have hbits := populationInputFields_bits r
  have hpoint := pointPacked_bits (entryPointRequest r true true)
  change natBitLength (entryPredicateRequest r).point ≤ r.call.n + 1 at hpoint
  have hpop := entryPopulation_bits r
  have hpop' : natBitLength (entryPopulationRequest r).value + 2 ≤ W := by
    dsimp only [S, entrySourceScale] at hscale
    omega
  have hpow : W < 2 ^ W := Nat.lt_two_pow_self
  refine ⟨by omega, (show _ ≤ W by omega).trans_lt hpow,
    (show _ ≤ W by omega).trans_lt hpow, (show _ ≤ W by omega).trans_lt hpow,
    (show _ ≤ W by omega).trans_lt hpow, (show _ ≤ W by omega).trans_lt hpow,
    ?_, (show _ ≤ W by omega).trans_lt hpow, hpop',
    (show _ ≤ entryResources r by omega).trans hL,
    (show _ ≤ entryResources r by omega).trans hL,
    (show _ ≤ entryResources r by omega).trans hL,
    hcalls.1.trans hB, hcalls.2.1.trans hB, hcalls.2.2.trans hB⟩
  intro p hp
  have h := hbits p hp
  exact (show natBitLength p.2 + 2 ≤ W by omega).trans_lt hpow

/-- `prop:time`, paper/paper.tex: the funded
native program clock remains linear in one common reservation after
charging its three ordinary calls and every output framing step. -/
theorem entryProgram_steps_le {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (W : ℕ) (hW : entryResources r ≤ W) :
    3 * rawEntrySteps r W W + 8 ≤ 1000 * W := by
  have hn := entryResources_native r
  have hs := entryResources_scale r
  have he : evaluationSteps r W W = evaluationSteps r 0 0 + 6 * W := by
    unfold evaluationSteps
    omega
  unfold rawEntrySteps
  rw [he]
  omega

end NearQuarticWires.StageMainMask
