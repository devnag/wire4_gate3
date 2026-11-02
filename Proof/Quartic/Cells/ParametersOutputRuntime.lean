import Proof.Quartic.Cells.ParametersPrepWord
import Proof.Quartic.StageOutput.WordFunction

set_option autoImplicit false

namespace NearQuarticWires.Cells

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open StageOutput
open ParameterArithmetic

/-- The padded output word contains exactly the charged extra
cells, Step 5 and `prop:time`, paper/paper.tex. -/
theorem output_padded_length (r : OutputRequest) :
    r.padded.length = r.word.length + r.padding := by
  cases r with
  | inl q => rfl
  | inr d =>
    simp only [OutputRequest.padded, OutputRequest.word, OutputRequest.padding,
      Input.padded, List.length_cons, List.length_append, List.length_replicate]
    omega

/-- A fixed polynomial majorant for the entire physical Step 5
budget, including framing, both binary setups, and paid padding,
`prop:time`, paper/paper.tex. -/
def outputResourceMajorant (R : ℕ) : ℕ :=
  4 * (1600 * (R + 1) +
    4 * budgetOf VV 4 R (3 * (1000 * wdOf 4 R + 10 * R + 3000) + 2) + 12) +
  4 * (1600 * (2 * R + 1) +
    4 * budgetOf VV 4 (2 * R) (3000 * wdOf 4 (2 * R) + 3000) + 12) + 12

/-- The literal raw output budget is bounded by its polynomial
majorant whenever both the input length and paid padding are
bounded, `prop:time`, paper/paper.tex. -/
theorem rawOutputBudget_majorant (r : OutputRequest) (R : ℕ)
    (hL : r.word.length ≤ R) (hpad : r.padding ≤ R) :
    rawOutputBudget r ≤ outputResourceMajorant R := by
  have hp : r.padded.length ≤ 2 * R := by rw [output_padded_length]; omega
  unfold rawOutputBudget prepareBudget paddedOutputBudget paddingRunBudget arithmeticRunBudget
    outputResourceMajorant paddingSteps outputSteps budgetOf setupCost KC wdOf
  gcongr

/-- The scalar request and its padding are bounded by one
polynomial in the actual serialized call, uniformly over all
witnesses, `prop:time`, paper/paper.tex. -/
theorem output_request_resources (B1 B2 : ℕ) (c : Call) (w : List Bool) :
    let R := 200 * (preparationCoefficient B1 + 5) * ((callWord c).length + 1) ^ (B1 + 12)
    (outputRequest B1 B2 c w).word.length ≤ R ∧ (outputRequest B1 B2 c w).padding ≤ R := by
  classical
  let L := (callWord c).length
  let R := 200 * (preparationCoefficient B1 + 5) * (L + 1) ^ (B1 + 12)
  have hpow : L ≤ (L + 1) ^ (B1 + 12) := (Nat.le_succ L).trans
    (by simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos L) (by omega : 1 ≤ B1 + 12))
  have hscale : (L + 1) ^ (B1 + 12) ≤ R := by
    have h := Nat.mul_le_mul_right ((L + 1) ^ (B1 + 12))
      (show 1 ≤ 200 * (preparationCoefficient B1 + 5) by omega)
    simpa only [Nat.one_mul] using h
  refine ⟨?_, ?_⟩
  · rw [outputRequest_word]
    exact all_calls_mainWord_length B1 B2 c w
  · cases hd : Program.dispatch B1 B2 c with
    | none => simp only [outputRequest, hd, OutputRequest.padding]; omega
    | some p =>
      have hn : c.n ≤ L := dispatched_n_le_callWord hd
      simpa only [outputRequest, hd, OutputRequest.padding, selectedInput] using
        hn.trans (hpow.trans hscale)

/-- The complete composed output budget is polynomial in its
scalar resource bound, `prop:time`, paper/paper.tex. -/
theorem output_resource_majorant_polynomial (B1 : ℕ) :
    PolyB (fun L => outputResourceMajorant
      (200 * (preparationCoefficient B1 + 5) * (L + 1) ^ (B1 + 12))) := by
  unfold outputResourceMajorant budgetOf setupCost KC wdOf
  polyb

/-- The exact physical output word function satisfies the
polynomial-cost field of the counter, on every call and witness,
`prop:time`, paper/paper.tex. -/
theorem outputBudget_polynomial (B1 B2 : ℕ) : Program.PolyCost (StageOutput.outputBudget B1 B2) := by
  obtain ⟨K, e, hK⟩ := output_resource_majorant_polynomial B1
  refine ⟨K, e, ?_⟩
  intro c w
  obtain ⟨hL, hpad⟩ := output_request_resources B1 B2 c w
  exact (rawOutputBudget_majorant (outputRequest B1 B2 c w) _ hL hpad).trans (hK (callWord c).length)

end NearQuarticWires.Cells
