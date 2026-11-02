import Proof.Quartic.Reconstruct.PrintWidth
import Proof.Quartic.Reconstruct.EmitPack
import Proof.Quartic.StageMain.HeaderWidth

/-!
# The printing stage as a word function

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The printing program runs with the width `2^(c₁ L) a₁` read from the leading ones `L = 1 + |n|` of `gammaWord q`
(`leadOnes_gammaWord`); `c₁ = (B₂+8)(B₁+12)` and `a₁ = prepC B₁ + 4 (c+1)^3 + 64` (`printSizes`) cover the width
`printWidth q` of every child (`printWidth_le`). `printWF` is the stage as a `WordFunction`; its budget is the
compiled budget of `printRunCost`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord callWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

/-- The constant of the width of the printing stage. -/
noncomputable def printA (B1 : ℕ) : ℕ :=
  prepC B1 + 4 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 3 + 64

/-- The word sizes of the printing stage: width `2^(c₁ L) a₁`, no calls. -/
noncomputable def printSizes (B1 B2 : ℕ) : Sz := ⟨printA B1, prepE B1 B2, 0, 0, 0, 0⟩

theorem leadOnes_gammaWord (q : ChildRequest B1 B2) : leadOnes (gammaWord q) = 1 + natBitLength q.call.n := by
  rw [gammaWord_split]
  exact StageMain.taggedCall_header_width q.call _

/-- **The width of the run covers the printing stage of every child.** -/
theorem printWidth_le (q : ChildRequest B1 B2) :
    printWidth q ≤ (printSizes B1 B2).W (leadOnes (gammaWord q)) := by
  set c := Cells.ParameterArithmetic.preparationCoefficient B1
  set X := (q.call.n + 1) ^ prepE B1 B2 with hX
  have hp : (prepWord B1 B2 q.call q.witness).length + 1 ≤ prepC B1 * X := prepWord_le q
  have hV := envelope_succ_le q
  have hX1 : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have h3 : (envelope q + 1) ^ 3 ≤ (c + 1) ^ 3 * X := by
    calc (envelope q + 1) ^ 3 ≤ ((c + 1) * (q.call.n + 1) ^ (B1 + 12)) ^ 3 := Nat.pow_le_pow_left hV 3
      _ = (c + 1) ^ 3 * (q.call.n + 1) ^ (3 * (B1 + 12)) := by rw [mul_pow, ← pow_mul, mul_comm (B1 + 12)]
      _ ≤ (c + 1) ^ 3 * X := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by unfold prepE; nlinarith))
  have hW : printWidth q ≤ printA B1 * X := by
    unfold printWidth printA
    have e : (prepC B1 + 4 * (c + 1) ^ 3 + 64) * X = prepC B1 * X + 4 * ((c + 1) ^ 3 * X) + 64 * X := by ring
    rw [e]
    omega
  have hX2 : X ≤ 2 ^ (prepE B1 B2 * (1 + natBitLength q.call.n)) := by
    calc X ≤ (2 ^ natBitLength q.call.n) ^ prepE B1 B2 :=
          Nat.pow_le_pow_left (NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl _) _
      _ = 2 ^ (natBitLength q.call.n * prepE B1 B2) := by rw [← pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  unfold Sz.W printSizes
  simp only
  rw [leadOnes_gammaWord]
  calc printWidth q ≤ printA B1 * X := hW
    _ ≤ printA B1 * 2 ^ (prepE B1 B2 * (1 + natBitLength q.call.n)) := Nat.mul_le_mul_left _ hX2
    _ = _ := by ring

/-- The run width of the printing stage of a child. -/
noncomputable def printW (B1 B2 : ℕ) (q : ChildRequest B1 B2) : ℕ := (printSizes B1 B2).W (leadOnes (gammaWord q))

/-- The budget of the printing stage. -/
noncomputable def printBudget (B1 B2 : ℕ) (q : ChildRequest B1 B2) : ℕ :=
  langBudget NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (printSizes B1 B2) VV MM (gammaWord q)
    (printRunCost q (printW B1 B2 q))

/-- **The printing stage** `gammaWord ↦ frame printsWord`. -/
noncomputable def printWF (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) gammaWord (fun q => frame (printsWord q)) (printBudget B1 B2) :=
  wordFunction_of_lang gammaWord (fun q => frame (printsWord q))
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (printSizes B1 B2) printsS
    (fun q => printRunCost q (printW B1 B2 q)) (fun q => by
      obtain ⟨b, n, hex, hn, hb⟩ := printsS_run
        (C := ctxOf NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (printSizes B1 B2) (gammaWord q)) q rfl
        (preBounds_of_le q _ (printWidth_le q)) (postBounds_of_le q _ (printWidth_le q))
      exact ⟨b, n, hex, hb, hn⟩) (fun q => by
      have := printWidth_le q
      unfold printWidth at this
      omega)

end NearQuarticWires.Reconstruct
