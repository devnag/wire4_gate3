import Proof.Quartic.Program.Output

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- The sound default has constant serialized size, `sec:params`,
paper/paper.tex. -/
theorem soundDefault_outputWord_length : (outputWord Algorithm.soundDefault).length ≤ 24 := by
  norm_num [Algorithm.soundDefault, outputWord, ratWord, NearCubicGates.Close.Interfaces.intWord,
    List.length_append, NearCubicGates.Close.CounterAsm.natWord_len', natBitLength]

/-- An exact zero-radius Boolean answer has constant serialized
size, `sec:params`, paper/paper.tex. -/
theorem bit_outputWord_length (b : Bool) : (outputWord (Builder.bitQ b, 0)).length ≤ 24 := by
  cases b <;> decide

/-- The closed zero-wire answer has constant serialized size even
when the encoded arity is arbitrarily large, `sec:params` and
`prop:time`, paper/paper.tex. -/
theorem closedValue_outputWord_length (c : Call) : (outputWord (Builder.closedValue c)).length ≤ 24 := by
  cases hk : c.kind with
  | single => simpa only [Builder.closedValue, hk] using bit_outputWord_length (Builder.constantValue c.first)
  | pair => simpa only [Builder.closedValue, hk] using
      bit_outputWord_length (xor (Builder.constantValue c.first) (Builder.constantValue c.second))
  | parity =>
    cases hp : Builder.oddParity c
    · simpa only [Builder.closedValue, hk, hp, Bool.false_eq_true, ↓reduceIte] using
        bit_outputWord_length (Builder.constantValue c.first)
    · simpa only [Builder.closedValue, hk, hp, ↓reduceIte] using
        (show (outputWord ((1 / 2 : ℚ), 0)).length ≤ 24 from by
          norm_num [outputWord, ratWord, NearCubicGates.Close.Interfaces.intWord,
            List.length_append, NearCubicGates.Close.CounterAsm.natWord_len', natBitLength])

/-- Every non-dispatched call carries a constant-sized final
interval, including parameter failure and zero-wire calls,
`sec:params` and `prop:time`, paper/paper.tex. This does not require arity to fit the call-word length. -/
theorem nondispatched_outputWord_length {B1 B2 : ℕ} (c : Call) (w : List Bool)
    (hd : Program.dispatch B1 B2 c = none) :
    (outputWord (Program.admittedValue B1 B2 Builder.value c w)).length ≤ 24 := by
  classical
  by_cases ha : Transfer.Admitted4 B1 B2 c
  · rw [Program.admittedValue_of_admitted _ ha]
    have hs := Builder.Shaped.of_admitted ha
    have hn : ¬ c.n < 4 := by have := ha.1; omega
    by_cases hW : Transfer.callWires c = 0
    · simpa only [Builder.value, if_pos hs, if_neg hn, if_pos hW] using closedValue_outputWord_length c
    · have hp : prepare (Builder.callInput c) = none := by
        cases hp : prepare (Builder.callInput c) with
        | none => rfl
        | some p =>
          unfold Program.dispatch at hd
          rw [if_pos ⟨ha, hW⟩] at hd
          split at hd
          · contradiction
          · rename_i hnone
            rw [hp] at hnone
            contradiction
      unfold Builder.value
      rw [if_pos hs, if_neg hn, if_neg hW]
      split
      · exact soundDefault_outputWord_length
      · rename_i p hsome
        rw [hp] at hsome
        contradiction
  · rw [Program.admittedValue_of_not_admitted _ ha]
    exact soundDefault_outputWord_length

/-- The false-tag branch of the word after Step 4 has a constant
length bound, `prop:time`, paper/paper.tex. -/
theorem nondispatched_mainWord_length {B1 B2 : ℕ} (c : Call) (w : List Bool)
    (hd : Program.dispatch B1 B2 c = none) : (Program.mainWord B1 B2 c w).length ≤ 25 := by
  have h := nondispatched_outputWord_length c w hd
  simpa only [Program.mainWord, Program.stageWord, hd, List.length_cons] using Nat.add_le_add_right h 1

end NearQuarticWires.Cells
