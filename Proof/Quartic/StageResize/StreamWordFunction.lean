import Proof.Quartic.StageResize.StreamProgram

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the actual width
prefix supplies workspace independently of the number of source fields. -/
theorem stream_input_leadOnes (r : StreamResizeRequest) :
    leadOnes r.word = natBitLength r.outputWidth := by
  unfold StreamResizeRequest.word
  rw [List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

theorem streamWidth (r : StreamResizeRequest) :
    r.outputWidth + natBitLength r.outputWidth + 4 ≤ resizeSizes.W (leadOnes r.word) := by
  have hv := lt_natBitLength r.outputWidth
  have hl := Nat.lt_two_pow_self (n := natBitLength r.outputWidth)
  have hp := Nat.one_le_two_pow (n := natBitLength r.outputWidth)
  simp only [resizeSizes, Sz.W, one_mul, stream_input_leadOnes]
  omega

/-- `prop:time`, paper/paper.tex: genuine cold
ordinary compilation charges headers, all actual source fields, output
and head reset; the empty callee contains no supplied resize oracle. -/
noncomputable def StreamResizeRequest.budget (r : StreamResizeRequest) : ℕ :=
  langBudget resizeCallee resizeSizes VV MM r.word (streamSourceClock r)

/-- `lem:print`, paper/paper.tex: a cold ordinary
machine resizes the entire actual raw record stream with one paid end
bit, no runtime source width/count/value fields and no output oracle. -/
noncomputable def streamResizeWordFunction :
    WordFunction StreamResizeRequest StreamResizeRequest.word
      StreamResizeRequest.output StreamResizeRequest.budget :=
  wordFunction_of_lang StreamResizeRequest.word StreamResizeRequest.output
    resizeCallee resizeSizes streamProgram streamSourceClock (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := streamProgram_run
        (ctxOf resizeCallee resizeSizes r.word) r rfl (streamWidth r)
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := streamWidth r
      omega)

end NearQuarticWires.StageResize
