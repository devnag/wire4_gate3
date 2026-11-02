import Proof.Quartic.Reconstruct.PrintWp

/-!
# The input of the printing stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `sec:params`.

The input of the printing stage is `gammaWord q`: the tag of a dispatched call, the call, the parameters, the framed
witness prefix, the framed certified bits, the framed seed prefix and the framed coefficient table
(`gammaWord_split`); the word `prepWord` handed to every printed table is its first part (`prepWord_split`). The
witness prefix has `k + (J+1)(G_1+G_2)` bits with `G_j = (ω_j - 1)/16` (`witnessPrefix_length`), and
`(ω_j - 1)/2 = 2mG_j` (`omega_half`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (callWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The witness prefix of a child. -/
noncomputable def wpOf (q : ChildRequest B1 B2) : List Bool := witnessPrefix q.call q.selected.1 q.witness

/-- **The input of the printing stage.** -/
theorem gammaWord_split (q : ChildRequest B1 B2) :
    gammaWord q = true :: (callWord q.call ++ (parametersWord q.selected.1 ++ (frame (wpOf q) ++
      (frame (certifiedBits q.cellCall) ++ (frame q.seedPrefix ++ gammaTableWord q))))) := by
  unfold gammaWord childInput certWord stageWord wpOf
  rw [q.dispatched]
  simp only [List.cons_append, List.append_assoc]
  rfl

/-- **The word handed to every printed table.** -/
theorem prepWord_split (q : ChildRequest B1 B2) :
    prepWord B1 B2 q.call q.witness = true :: (callWord q.call ++ (parametersWord q.selected.1 ++ frame (wpOf q))) := by
  unfold prepWord stageWord wpOf
  rw [q.dispatched]
  simp only [List.append_assoc]

theorem omega_eq (q : ChildRequest B1 B2) (j : Fin 2) :
    (if j = 0 then q.selected.1.omega1 else q.selected.1.omega2) = 16 * Builder.occurrences q.call j + 1 := by
  have e1 := (rules q).omega1_eq
  have e2 := (rules q).omega2_eq
  have hm := (rules q).m_eq
  rw [hm] at e1 e2
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, if_true]
    rw [e1]; rfl
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, if_false]
    rw [e2]; rfl

/-- `(ω_j - 1)/2 = 2mG_j`. -/
theorem omega_half (q : ChildRequest B1 B2) :
    (q.selected.1.omega1 - 1) / 2 = 2 * Algorithm.traceOrder * Builder.occurrences q.call 0 ∧
      (q.selected.1.omega2 - 1) / 2 = 2 * Algorithm.traceOrder * Builder.occurrences q.call 1 := by
  have h0 := omega_eq q 0
  have h1 := omega_eq q 1
  simp only [Fin.isValue, if_true, one_ne_zero, if_false] at h0 h1
  have e : 2 * Algorithm.traceOrder = 8 := rfl
  rw [e, h0, h1]
  omega

/-- **The length of the witness prefix.** -/
theorem witnessPrefix_length (q : ChildRequest B1 B2) :
    (wpOf q).length = q.selected.1.k + (q.selected.1.J + 1) *
      ((q.selected.1.omega1 - 1) / 2 / 2 / 2 / 2 + (q.selected.1.omega2 - 1) / 2 / 2 / 2 / 2) := by
  have h0 := omega_eq q 0
  have h1 := omega_eq q 1
  simp only [Fin.isValue, if_true, one_ne_zero, if_false] at h0 h1
  unfold wpOf witnessPrefix witnessReadLength
  rw [List.length_ofFn, h0, h1]
  congr 2
  omega

end NearQuarticWires.Reconstruct
