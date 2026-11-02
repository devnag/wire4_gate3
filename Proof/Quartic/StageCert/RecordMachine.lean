import Proof.Quartic.StageCert.RecordRun
import Proof.Gates.Solve.Machine
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary

/-- `prop:time`, paper/paper.tex: the width header for one
signed moment and its natural threshold. -/
def recordWidth (r : ℤ × ℕ) : ℕ :=
  natBitLength (if r.1 < 0 then 1 else 0) + natBitLength r.1.natAbs + natBitLength r.2 + 8

/-- `sec:algorithm`, paper/paper.tex: the concrete single-record
input uses a width header and the existing signed integer codec. -/
def recordInput (r : ℤ × ℕ) : List Bool :=
  natWord (recordWidth r) ++ NearCubicGates.Close.Interfaces.intWord r.1 ++ natWord r.2

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: the framed
Boolean result of one literal strict moment test. -/
def recordOutput (r : ℤ × ℕ) : List Bool := frame [decide (r.1 < (r.2 : ℤ))]

/-- `sec:algorithm`, paper/paper.tex: no external call is made by
the strict-test program; the common language compiler uses this fixed callee. -/
noncomputable def recordCallee : Callee := Callee.ofSolve NearCubicGates.Close.Solve.solveMachine

/-- `prop:time`, paper/paper.tex: arithmetic word size is
linear in the decoded width header. -/
def recordSizes : Sz := ⟨16, 1, 0, 0, 0, 0⟩

/-- `prop:time`, paper/paper.tex: the concrete compiler
context contains every bit read in a strict test. -/
theorem record_context_width (r : ℤ × ℕ) :
    recordWidth r + 4 ≤ (ctxOf recordCallee recordSizes (recordInput r)).Wd := by
  change recordWidth r+4 ≤ 2^(1*leadOnes (recordInput r))*16
  have he : leadOnes (recordInput r) = natBitLength (recordWidth r) := by
    unfold recordInput
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord (recordWidth r)
        (NearCubicGates.Close.Interfaces.intWord r.1 ++ natWord r.2)
  rw [he, Nat.one_mul]
  have h := lt_natBitLength (recordWidth r)
  omega

/-- `prop:time`, paper/paper.tex: the explicit compiled
single-record budget, including setup, decoding, comparison and output. -/
noncomputable def recordBudget (r : ℤ × ℕ) : ℕ :=
  langBudget recordCallee recordSizes VV MM (recordInput r) (1000*(recordWidth r+1))

/-- `sec:algorithm`, paper/paper.tex: a physical word function
computes a strict signed moment test, with no conditional-test oracle. -/
noncomputable def recordMachine : WordFunction (ℤ × ℕ) recordInput recordOutput recordBudget :=
  wordFunction_of_lang recordInput recordOutput recordCallee recordSizes recordProgram
    (fun r => 1000*(recordWidth r+1)) (by
      intro r
      obtain ⟨b, n, he, hn, hb⟩ := recordProgram_run
        (ctxOf recordCallee recordSizes (recordInput r)) (recordWidth r) r.1 r.2 rfl
        (record_context_width r) (by unfold recordWidth; omega)
        (by unfold recordWidth; omega) (by unfold recordWidth; omega)
      exact ⟨b, n, he, hb, hn⟩) (by
      intro r
      have := record_context_width r
      change 1 ≤ (ctxOf recordCallee recordSizes (recordInput r)).Wd
      omega)

end NearQuarticWires.StageCert
