import Proof.Quartic.Greedy.Assemble
import Proof.Quartic.Program.Main

/-!
# `thm:main` with the `greedy` stage assembled from its parts

Paper: `thm:main`, paper/paper.tex; `thm:counter`; `sec:algorithm`;
`prop:time`.

`OtherStages` collects the stages `prep`, `cert`, `main` and `output` of the counter program with their costs, and
`GreedyParts` the parts of the `greedy` stage. `finalStatement4_of_parts` derives the statement from the eight
intermediate inputs (`NineInputs`), the mathematical half of the counter, and these parts.
-/

set_option autoImplicit false

namespace NearQuarticWires.Greedy

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces
open NearQuarticWires.Program

/-- **The stages of the counter program other than `greedy`**, with their costs (`sec:algorithm`, paper/paper.tex, and `prop:time`): parameter preparation, Steps 1–2, Step 4 and Step 5. -/
structure OtherStages (B1 B2 : ℕ) where
  /-- The cost of `prep`. -/
  prepBudget : Call → List Bool → ℕ
  /-- Parameter preparation and the witness prefix. -/
  prep : WordFunction (Call × List Bool) requestWord (fun r => frame (prepWord B1 B2 r.1 r.2))
    (fun r => prepBudget r.1 r.2)
  prepCost : PolyCost prepBudget
  /-- The cost of `cert`. -/
  certBudget : Call → List Bool → ℕ
  /-- Steps 1–2. -/
  cert : WordFunction (Call × List Bool) (fun r => prepWord B1 B2 r.1 r.2)
    (fun r => frame (certWord B1 B2 r.1 r.2)) (fun r => certBudget r.1 r.2)
  certCost : LedgerCost B1 B2 certBudget
  /-- The cost of `main`. -/
  mainBudget : Call → List Bool → ℕ
  /-- Step 4. -/
  main : WordFunction (Call × List Bool) (fun r => greedyWord B1 B2 r.1 r.2)
    (fun r => frame (mainWord B1 B2 r.1 r.2)) (fun r => mainBudget r.1 r.2)
  mainCost : LedgerCost B1 B2 mainBudget
  /-- The cost of `output`. -/
  outputBudget : Call → List Bool → ℕ
  /-- Step 5. -/
  output : WordFunction (Call × List Bool) (fun r => mainWord B1 B2 r.1 r.2)
    (fun r => outputWord (admittedValue B1 B2 Builder.value r.1 r.2)) (fun r => outputBudget r.1 r.2)
  outputCost : PolyCost outputBudget

/-- The machine components of the counter from the other stages and the parts of `greedy`. -/
noncomputable def OtherStages.withGreedy {B1 B2 : ℕ} (O : OtherStages B1 B2) (G : GreedyParts B1 B2) :
    MachineComponents B1 B2 :=
  machineComponentsOfParts O.prepBudget O.prep O.prepCost O.certBudget O.cert O.certCost G O.mainBudget O.main
    O.mainCost O.outputBudget O.output O.outputCost

/-- **`thm:main` from the eight inputs (`NineInputs`), the mathematical half of the counter, the stages other than `greedy`, and the
parts of `greedy`** (the control of the `S` rounds, the controls of the two stages of a child evaluation, and the
three subroutines with their costs). -/
theorem finalStatement4_of_parts (inputs : NearCubicGates.Close.NineInputs)
    (hmath : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → ∃ M : Builder.CounterMath4 B1 B2, M.value = Builder.value)
    (hparts : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (OtherStages B1 B2) ∧ Nonempty (GreedyParts B1 B2)) :
    NearQuarticWires.Statement.FinalStatement4 :=
  finalStatement4_of_components inputs hmath fun B1 B2 h1 h2 =>
    let ⟨⟨O⟩, ⟨G⟩⟩ := hparts B1 B2 h1 h2
    ⟨O.withGreedy G⟩

end NearQuarticWires.Greedy
