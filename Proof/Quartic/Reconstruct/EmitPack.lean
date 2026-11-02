import Proof.Quartic.Reconstruct.EmitRun
import Proof.Gates.CounterMachine.PrefixFinal

/-!
# The emission stage as a word function

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The emission program runs with the width `2^(c₁ L) a₁` read from the leading ones `L = |n|` of the gathered word;
`a₁ = 100026 (c+1)^5`, `c₁ = 5 (B₁ + 12)` (`emitSizes`) cover the width `emitWidth q` of every child
(`emitWidth_le`). `emitWF` is the stage as a `WordFunction`; its budget is the compiled budget of `emitRunCost`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicWires.RepairOrdinary (WordFunction frame)

variable {B1 B2 : ℕ}

/-- The word sizes of the emission stage: width `2^(c₁ L) a₁`, no calls. -/
def emitSizes (B1 : ℕ) : Sz :=
  ⟨100026 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) ^ 5, 5 * (B1 + 12), 0, 0, 0, 0⟩

theorem leadOnes_gatheredWord (q : ChildRequest B1 B2) : leadOnes (gatheredWord q) = natBitLength q.call.n := by
  unfold gatheredWord contextWord
  simp only [List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

/-- The envelope of a child is at most `(c + 1)(n + 1)^(B₁+12) - 1`. -/
theorem envelope_succ_le (q : ChildRequest B1 B2) :
    envelope q + 1 ≤ (Cells.ParameterArithmetic.preparationCoefficient B1 + 1) * (q.call.n + 1) ^ (B1 + 12) := by
  rw [envelope_eq]
  have : 1 ≤ (q.call.n + 1) ^ (B1 + 12) := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- **The width of the run covers the emission of every child.** -/
theorem emitWidth_le (q : ChildRequest B1 B2) :
    emitWidth q ≤ (emitSizes B1).W (leadOnes (gatheredWord q)) := by
  set c := Cells.ParameterArithmetic.preparationCoefficient B1
  set V := envelope q
  have hV := envelope_succ_le q
  have h1 : 1 ≤ V + 1 := by omega
  have h2 : (V + 1) ^ 2 ≤ (V + 1) ^ 5 := Nat.pow_le_pow_right h1 (by norm_num)
  have h3 : 1 ≤ (V + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  have h4 : emitWidth q ≤ 100026 * (V + 1) ^ 5 := by
    show 100000 * (V + 1) ^ 5 + 6 * (V + 1) ^ 2 + 20 ≤ _; omega
  have h5 : (V + 1) ^ 5 ≤ (c + 1) ^ 5 * (q.call.n + 1) ^ (5 * (B1 + 12)) := by
    calc (V + 1) ^ 5 ≤ ((c + 1) * (q.call.n + 1) ^ (B1 + 12)) ^ 5 := Nat.pow_le_pow_left hV 5
      _ = (c + 1) ^ 5 * (q.call.n + 1) ^ (5 * (B1 + 12)) := by rw [mul_pow, ← pow_mul, mul_comm (B1 + 12)]
  have h6 : (q.call.n + 1) ^ (5 * (B1 + 12)) ≤ 2 ^ (5 * (B1 + 12) * natBitLength q.call.n) := by
    rw [pow_mul' 2]
    exact Nat.pow_le_pow_left (NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl _) _
  unfold Sz.W emitSizes
  simp only
  rw [leadOnes_gatheredWord]
  calc emitWidth q ≤ 100026 * ((c + 1) ^ 5 * (q.call.n + 1) ^ (5 * (B1 + 12))) := h4.trans (Nat.mul_le_mul_left _ h5)
    _ ≤ 100026 * ((c + 1) ^ 5 * 2 ^ (5 * (B1 + 12) * natBitLength q.call.n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h6)
    _ = _ := by ring

/-- The budget of the emission stage. -/
noncomputable def emitBudget (B1 : ℕ) (q : ChildRequest B1 B2) : ℕ :=
  langBudget NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) VV MM (gatheredWord q)
    (emitRunCost q ((emitSizes B1).W (leadOnes (gatheredWord q))))

/-- **The emission stage** `gatheredWord ↦ frame systemsWord`. -/
noncomputable def emitWF (B1 B2 : ℕ) :
    WordFunction (ChildRequest B1 B2) gatheredWord (fun q => frame (systemsWord q)) (emitBudget B1) :=
  wordFunction_of_lang gatheredWord (fun q => frame (systemsWord q))
    NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) emitS
    (fun q => emitRunCost q ((emitSizes B1).W (leadOnes (gatheredWord q)))) (fun q => by
      obtain ⟨b, n, hex, hn, hb⟩ := emitS_run q
        (ctxOf NearCubicGates.Close.CounterMachine.PrefixProg.noCallee (emitSizes B1) (gatheredWord q)) rfl
        (emitWidth_le q)
      exact ⟨b, n, hex, hb, hn⟩) (fun q => by
      have := emitWidth_le q
      unfold emitWidth at this
      omega)

end NearQuarticWires.Reconstruct
