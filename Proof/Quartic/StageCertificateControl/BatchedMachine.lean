import Proof.Quartic.StageCertificateControl.BatchedTables
import Proof.Gates.Expand.PolyTabPack

/-!
# The actual counted table-batch word function

Paper: `sec:algorithm`, paper/paper.tex,
`lem:print`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab

/-- `prop:time`, paper/paper.tex: the real
counted batch and its global parallel head return have one full clock. -/
def batchedMachineBudget {I : Type} {indexedInput : I→List Bool}
    (F : StagePrint.PoolFamily I indexedInput) (payload : I→List Bool) (budget : I→ℕ)
    (countBudget : ℕ) : ℕ :=
  2*batchedTablesCost F payload budget countBudget+2

/-- `sec:algorithm`, `lem:print`, and `prop:time`, paper/paper.tex: the fixed physical
program computes the count and the complete table batch from the cold
original preparation. Its final parallel head return is included in
the budget, and the exact native payload bytes remain unchanged. -/
noncomputable def batchedTablesWordFunction {Request I : Type}
    {source : Request→List Bool} {count countBudget : Request→ℕ}
    {indexedInput payload : I→List Bool} {budget : I→ℕ}
    (counter : WordFunction Request source
      (fun r => frame (RepairRepresentation.natWord (count r))) countBudget)
    (provider : WordFunction I indexedInput (fun i => frame (payload i)) budget)
    (hq : counter.program.tapeCount≤provider.program.tapeCount)
    (families : Request→StagePrint.PoolFamily I indexedInput)
    (hsource : ∀r,(families r).source=source r)
    (hcount : ∀r,(families r).count=count r) :
    WordFunction Request source
      (fun r => frame (flattenedPoolWord (families r).source
        ((families r).caches payload) (families r).count))
      (fun r => batchedMachineBudget (families r) payload budget (countBudget r)) :=
  wordFunction_of_ideal (batchedTablesProgram provider.program counter.program hq)
    (StagePrint.poolFinal provider.program) (by simp [StagePrint.poolFinal])
    (fun r => batchedTablesCapacity (families r) payload budget (countBudget r))
    (fun _ _ => 0)
    (fun r => batchedTablesCost (families r) payload budget (countBudget r))
    (by intro r;exact Nat.le_refl _)
    (by
      intro r
      refine ⟨rfl,?_⟩
      exact batchedTables_exec counter provider hq r (families r) (hsource r) (hcount r))

end NearQuarticWires.StageCertificateControl
