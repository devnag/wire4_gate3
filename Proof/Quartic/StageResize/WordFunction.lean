import Proof.Quartic.StageResize.Program
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: field extension
has no external subroutine or supplied value computation. -/
noncomputable def resizeCallee : Callee :=
  ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    wordFunction_of_wmx (WMX.skip : WMX 1 0) 1 (by decide) (fun _ => 0) (fun e => e.elim)⟩

def resizeSizes : Sz := ⟨64, 1, 0, 0, 0, 0⟩

theorem input_leadOnes (r : ResizeRequest) : leadOnes r.word = natBitLength r.outputWidth := by
  unfold ResizeRequest.word
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

/-- `prop:time`, paper/paper.tex: the actual
target-width codec supplies all workspace for parsing and counters. -/
theorem resizeWidth (r : ResizeRequest) :
    r.outputWidth + natBitLength r.outputWidth + 4 ≤ resizeSizes.W (leadOnes r.word) := by
  have hv := lt_natBitLength r.outputWidth
  have hl := Nat.lt_two_pow_self (n := natBitLength r.outputWidth)
  have hp := Nat.one_le_two_pow (n := natBitLength r.outputWidth)
  simp only [resizeSizes, Sz.W, one_mul, input_leadOnes]
  omega

/-- `prop:time`, paper/paper.tex: the ordinary
budget includes cold workspace setup, compiled bit operations, output
and final head reset. -/
noncomputable def ResizeRequest.budget (r : ResizeRequest) : ℕ :=
  langBudget resizeCallee resizeSizes VV MM r.word (sourceClock r)

/-- `lem:print`, paper/paper.tex: a genuine cold
ordinary machine zero-extends the actual framed fixed-width field,
returning exactly one target frame for every valid request. -/
noncomputable def resizeWordFunction :
    WordFunction ResizeRequest ResizeRequest.word ResizeRequest.output ResizeRequest.budget :=
  wordFunction_of_lang ResizeRequest.word ResizeRequest.output resizeCallee resizeSizes
    program sourceClock (by
      intro r
      obtain ⟨b, n, he, hn, ho⟩ := program_run
        (ctxOf resizeCallee resizeSizes r.word) r rfl (resizeWidth r)
      exact ⟨b, n, he, ho, hn⟩) (by
      intro r
      have h := resizeWidth r
      omega)

end NearQuarticWires.StageResize
