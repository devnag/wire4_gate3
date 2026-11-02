import Proof.Quartic.StageMain.MainProgram

/-!
# Ordinary-machine packaging of the complete main program

Step 4 of `sec:algorithm`, paper/paper.tex,
is executed after the once-only primitive-field construction of
`imp:seed`. The budgets include both physical stream
composition passes, arithmetic setup, the entire main program, and
teardown. Numeric size conditions are stated explicitly below.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open Controller SampleCells

noncomputable def cachedMainBudget {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    (sizes : Sz) (T : Call → List Bool → ℕ) (c : Call) (w : List Bool) : ℕ :=
  langBudget (sampleTaggedCallee f) sizes VV MM (cachedMainWord B1 B2 c w)
    (sourceSteps B1 B2 c w (T c w))

noncomputable def cachedMainWordFunction_of_bounds {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    (sizes : Sz) (T : Call → List Bool → ℕ)
    (hwidth : ∀ c w, 64 ≤ sizes.W (leadOnes (cachedMainWord B1 B2 c w)))
    (hactive : ∀ (c : Call) (w : List Bool) (p : Program.Selected c)
      (hd : Program.dispatch B1 B2 c = some p),
      let l := leadOnes (cachedMainWord B1 B2 c w)
      ActiveCapacity f hd w (sizes.W l) (sizes.Lk l) (sizes.Bk l) (T c w)) :
    WordFunction (Call × List Bool) (fun r => cachedMainWord B1 B2 r.1 r.2)
      (fun r => frame (Program.mainWord B1 B2 r.1 r.2)) (fun r => cachedMainBudget f sizes T r.1 r.2) := by
  exact wordFunction_of_lang
    (fun r : Call × List Bool => cachedMainWord B1 B2 r.1 r.2)
    (fun r : Call × List Bool => frame (Program.mainWord B1 B2 r.1 r.2))
    (sampleTaggedCallee f) sizes mainProgram
    (fun r => sourceSteps B1 B2 r.1 r.2 (T r.1 r.2)) (by
      intro r
      let l := leadOnes (cachedMainWord B1 B2 r.1 r.2)
      obtain ⟨b, n, he, hn, ho⟩ := mainProgram_run_of_bounds f r.1 r.2 (sizes.W l)
        (cachedMainWord B1 B2 r.1 r.2) (sizes.Lk l) (sizes.Bk l) (T r.1 r.2) rfl
        (hwidth r.1 r.2) (hactive r.1 r.2)
      exact ⟨b, n, he, ho, hn⟩) (by intro r; have hh := hwidth r.1 r.2; omega)

noncomputable def mainBudgetOf {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    (sizes : Sz) (T : Call → List Bool → ℕ) (c : Call) (w : List Bool) : ℕ :=
  4 * retainedMainFieldCost B1 B2 c w + 4 * cachedMainBudget f sizes T c w + 12

noncomputable def mainWordFunction_of_bounds {B1 B2 : ℕ} {budget : EntryRequest B1 B2 → ℕ}
    (f : WordFunction (EntryRequest B1 B2) entryWord entryOutput budget)
    (sizes : Sz) (T : Call → List Bool → ℕ)
    (hwidth : ∀ c w, 64 ≤ sizes.W (leadOnes (cachedMainWord B1 B2 c w)))
    (hactive : ∀ (c : Call) (w : List Bool) (p : Program.Selected c)
      (hd : Program.dispatch B1 B2 c = some p),
      let l := leadOnes (cachedMainWord B1 B2 c w)
      ActiveCapacity f hd w (sizes.W l) (sizes.Lk l) (sizes.Bk l) (T c w)) :
    WordFunction (Call × List Bool) (fun r => Program.greedyWord B1 B2 r.1 r.2)
      (fun r => frame (Program.mainWord B1 B2 r.1 r.2)) (fun r => mainBudgetOf f sizes T r.1 r.2) :=
  Program.WordFunction.pipe (retainedMainFieldWordFunction B1 B2)
    (cachedMainWordFunction_of_bounds f sizes T hwidth hactive)

end NearQuarticWires.StageMain
