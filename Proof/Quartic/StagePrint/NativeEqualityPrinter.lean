import Proof.Quartic.StagePrint.NativeRequests

set_option autoImplicit false

namespace NearQuarticWires.StagePrint

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape

attribute [local irreducible] EquationRowRaw.machine EquationRowPrepare.machine

/-- `lem:print`, paper/paper.tex: the cold
two-cut input contains only the actual measured row count, actual
widths and the original equality-cut field stream. -/
def NativeStreamRequest.equalitySource (r : NativeStreamRequest) : List Bool :=
  EquationRowRaw.source r.equalityInput

/-- `lem:print` and `prop:time`, paper/paper.tex: retain the exact physical constructor clock rather
than replacing the equality census by a cubic count envelope. -/
def NativeStreamRequest.equalityBudget (r : NativeStreamRequest) : ℕ :=
  EquationRowFramed.budget r.equalityInput

/-- `lem:print`, paper/paper.tex: an actual
cold ordinary subroutine transforms the original signed equality
stream into its exact signed two-weak-cut body. Its temporary identity
header is explicit and performs no table evaluation. -/
noncomputable def nativeEqualityPrinter :
    WordFunction NativeStreamRequest NativeStreamRequest.equalitySource
      (fun r=>MatrixScoreBatch.physicalInput (EquationRow.request r.equalityInput))
      NativeStreamRequest.equalityBudget where
  program:=EquationRowFramed.program
  realizes:=by
    intro r
    obtain ⟨actual,ha,hout,hh,ht⟩:=EquationRowFramed.framed_run r.equalityInput
    refine ⟨actual,?_,?_⟩
    · change run EquationRowFramed.machine r.equalityBudget
        (EquationRowFramed.program.inputTapes r.equalitySource)=some actual
      dsimp only [NativeStreamRequest.equalitySource,NativeStreamRequest.equalityBudget]
      rw [EquationRowFramed.input_eq]
      exact ha
    · change actual.final.tapes (128 : Fin 130)=_
      exact hout

end NearQuarticWires.StagePrint
