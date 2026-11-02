import Proof.Quartic.StageMainMask.EntryRequests
import Proof.Quartic.StageMainMask.PredicateFramed

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StageMain StagePullback

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the predicate request uses the physically generated both-error point
and the complete original call word. -/
noncomputable def entryPredicateRequest {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    PredicateRequest where
  call := r.call
  point := (entryPointRequest r true true).packed
  arity_le_word := by
    have h := Cells.dispatched_n_le_callWord r.dispatched
    simp only [List.length_append]
    omega

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the raw circuit subroutine reply is the exact required original
sample predicate, including the complete original top gates. -/
theorem entryPredicateRequest_value {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPredicateRequest r).value = entryPredicate r := by
  change r.call.predicate (packedPoint r.call.n (entryPointRequest r true true).packed) = _
  have hp := packedPoint_pointRequest (entryPointRequest r true true)
  exact (congrArg r.call.predicate hp).trans (entryPointRequest_predicate r)

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: the exact Boolean sampled mask is
the shared structural flag conjoined with the actual original selected
population comparison against the selected integer cutoff. -/
theorem entryMask_eq_replies {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    entryMask r = (structuralBit (entryStructuralRequest r) &&
      decide ((entryPopulationRequest r).value ≤ r.selected.1.tau)) := by
  change decide (Mask.mask (((entryCall r).column r.column).structural (entryPosition r))
    r.selected.1.tau (((entryCall r).column r.column).X (entryPosition r)) = 1) = _
  rw [← entryStructuralRequest_bit r, ← entryPopulationRequest_value r]
  cases structuralBit (entryStructuralRequest r) <;>
    by_cases h : (entryPopulationRequest r).value ≤ r.selected.1.tau <;>
    simp [Mask.mask, h]

end NearQuarticWires.StageMainMask
