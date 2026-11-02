import Proof.Quartic.StageMainMask.Sizes
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: one fixed native step allowance
comes only from the literal original arity header and pays all actual
source, point, three-subroutine and framed-output work. -/
noncomputable def entryStepLimit {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  1000 * (entrySizes B1 B2).W (leadOnes (entryWord r))

/-- `prop:time`, paper/paper.tex: the complete
ordinary Entry clock includes source and binary workspace setup, all
actual helper call banks, framed output and final head restoration. -/
noncomputable def entryBudget {B1 B2 : ℕ} (r : EntryRequest B1 B2) : ℕ :=
  langBudget (entryCallee B1 B2) (entrySizes B1 B2) VV MM (entryWord r) (entryStepLimit r)

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
one genuine cold ordinary machine reads the literal original Entry
word and returns its exact complete predicate and mask. All original
points, source records, scalar capacities and helper executions are
derived and paid; no independent point or helper provider is assumed. -/
noncomputable def entryWordFunction (B1 B2 : ℕ) :
    WordFunction (EntryRequest B1 B2) entryWord entryOutput entryBudget :=
  wordFunction_of_lang entryWord entryOutput (entryCallee B1 B2) (entrySizes B1 B2)
    entryProgram entryStepLimit (by
      intro r
      let W := (entrySizes B1 B2).W (leadOnes (entryWord r))
      have hr : entryResources r ≤ W := entrySizes_resources r
      have hscale := entryResources_scale r
      have hs := entrySourceScale_bounds r
      have hwidth : (entryWord r).length + 2 ≤ W := by omega
      have h64 : 64 ≤ W := entrySizes_min B1 B2 _
      have hnwidth : r.call.n + 4 ≤ W := by omega
      have hcap := entryCallCapacity_of_resources r W W W hr hr hr
      obtain ⟨b, n, he, hn, ho⟩ := entryProgram_run r W W W hwidth h64 hnwidth hcap
      exact ⟨b, n, he, ho, hn.trans (entryProgram_steps_le r W hr)⟩) (by
        intro r
        exact le_trans (by decide) (entrySizes_min B1 B2 _))

end NearQuarticWires.StageMainMask
