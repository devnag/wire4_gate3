import Proof.Quartic.Reconstruct.GatherProgRunQ

/-!
# The gathering stage within `K (n+1)^e` times its cost

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

`gatherWF` is the gathering program as a word function (`wordFunction_of_lang`, the sizes `emitSizes` of the
emission stage). Its run costs at most `10^6 U^3` times the cost `systemsCost` of the stage, `U` the scale of the
child (`runCostQ_le`), so its budget is at most `gatherK B₁ (n+1)^{gatherE B₁} systemsCost q` (`gatherBudget_le`).
**`gatherStage`** is the `gather` argument of `SystemsSplit.systemsOfSplit`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

theorem leadOnes_tablesWord (q : ChildRequest B1 B2) : leadOnes (tablesWord q) = natBitLength q.call.n := by
  unfold tablesWord contextWord
  simp only [List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

theorem gatherWidth_le (q : ChildRequest B1 B2) : emitWidth q ≤ (emitSizes B1).W (leadOnes (tablesWord q)) := by
  rw [leadOnes_tablesWord, ← leadOnes_gatheredWord]; exact emitWidth_le q

/-- The budget of the gathering stage. -/
noncomputable def gatherBudget (B1 : ℕ) (q : ChildRequest B1 B2) : ℕ :=
  langBudget NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) VV MM (tablesWord q) (runCostQ q)

/-- **The gathering stage** `tablesWord ↦ frame gatheredWord`. -/
noncomputable def gatherWF (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) tablesWord (fun q => frame (gatheredWord q)) (gatherBudget B1) :=
  wordFunction_of_lang tablesWord (fun q => frame (gatheredWord q))
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) gatherS (fun q => runCostQ q)
    (fun q => by
      obtain ⟨b, n, hex, hn, hb⟩ := gatherS_runQ q
        (ctxOf NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) (tablesWord q)) rfl
        (gatherWidth_le q)
      exact ⟨b, n, hex, hb, hn⟩) (fun q => by
      have := gatherWidth_le q
      unfold emitWidth at this
      omega)

end NearQuarticWires.Reconstruct.GatherProg
