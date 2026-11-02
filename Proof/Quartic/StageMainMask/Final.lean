import Proof.Quartic.StageMainMask.EntryBudget
import Proof.Quartic.StageMain.MainSizes
import Proof.Quartic.StageMain.MainLedger

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces

private theorem exists_mainArityPair (B1 B2 : ℕ) :
    ∃ p : ℕ × ℕ, ∀ r : StageMain.EntryRequest B1 B2,
      entryBudget r ≤ p.1 * (r.call.n + 1) ^ p.2 := by
  obtain ⟨K, d, h⟩ := entryBudget_arity B1 B2
  exact ⟨(K, d), h⟩

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the proved actual Entry clock
fixes one pair of original-arity constants for the entire Main machine. -/
noncomputable def mainArityPair (B1 B2 : ℕ) : ℕ × ℕ :=
  Classical.choose (exists_mainArityPair B1 B2)

/-- `prop:time`, paper/paper.tex: the chosen
fixed Main constants fund the complete actual Entry machine uniformly
over every original source, witness, column and field sample. -/
theorem mainArityPair_spec (B1 B2 : ℕ) (r : StageMain.EntryRequest B1 B2) :
    entryBudget r ≤ (mainArityPair B1 B2).1 * (r.call.n + 1) ^ (mainArityPair B1 B2).2 :=
  Classical.choose_spec (exists_mainArityPair B1 B2) r

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the complete actual Main budget
includes its source acquisition, field setup, sample and column loops,
all actual Entry calls and exact final Main-record serialization. -/
noncomputable def mainBudget (B1 B2 : ℕ) : Call → List Bool → ℕ :=
  StageMain.mainBudgetWithEntry (entryWordFunction B1 B2)
    (mainArityPair B1 B2).1 (mainArityPair B1 B2).2

/-- Step 4 of `sec:algorithm`, `def:mask` and `prop:time`,
paper/paper.tex:
one actual cold ordinary Main machine reads the literal original greedy
word and writes the exact framed Main word. Its numeric Entry supplier
is the complete original source and four-point machine proved here,
without an assumed point, gate-value, predicate or mask provider. -/
noncomputable def main (B1 B2 : ℕ) :
    WordFunction (Call × List Bool) (fun r => Program.greedyWord B1 B2 r.1 r.2)
      (fun r => frame (Program.mainWord B1 B2 r.1 r.2))
      (fun r => mainBudget B1 B2 r.1 r.2) :=
  StageMain.main_of_entry_bound (entryWordFunction B1 B2)
    (mainArityPair B1 B2).1 (mainArityPair B1 B2).2 (mainArityPair_spec B1 B2)

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the actual complete Main machine
satisfies the literal all-call ledger, including unsuccessful dispatch,
every original witness and all source and numeric helper executions. -/
theorem mainCost (B1 B2 : ℕ) : Program.LedgerCost B1 B2 (mainBudget B1 B2) :=
  StageMain.mainBudget_ledger (entryWordFunction B1 B2)
    (mainArityPair B1 B2).1 (mainArityPair B1 B2).2

end NearQuarticWires.StageMainMask
