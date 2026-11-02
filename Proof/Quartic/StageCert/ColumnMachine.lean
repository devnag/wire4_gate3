import Proof.Quartic.StageCert.ColumnRun
import Proof.Quartic.StageCert.RecordMachine

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicGates.Close.Cells
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces (listWord)

/-- `sec:algorithm`, paper/paper.tex: one column of signed moments,
with the finite scalar-width guards used by the binary arithmetic routines. -/
structure ColumnRequest where
  width : ℕ
  tests : List MomentRecord
  countFits : natBitLength tests.length ≤ width
  fieldsFit : ∀ r ∈ tests, natBitLength (if r.1<0 then 1 else 0) ≤ width ∧
    natBitLength r.1.natAbs ≤ width ∧ natBitLength r.2 ≤ width

/-- `sec:algorithm`, paper/paper.tex: the physical input to a
column reduction contains all signed records exactly once. -/
def columnInput (r : ColumnRequest) : List Bool :=
  natWord r.width ++ listWord momentRecordWord r.tests

/-- `sec:algorithm`, paper/paper.tex: one framed certificate bit. -/
noncomputable def columnOutput (r : ColumnRequest) : List Bool := frame [columnPass r.tests]

/-- `prop:time`, paper/paper.tex: the compiler width contains
every field read by the column reduction. -/
theorem column_context_width (r : ColumnRequest) :
    r.width+4 ≤ (ctxOf recordCallee recordSizes (columnInput r)).Wd := by
  change r.width+4 ≤ 2^(1*leadOnes (columnInput r))*16
  have he : leadOnes (columnInput r) = natBitLength r.width :=
    NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  rw [he, Nat.one_mul]
  have h := lt_natBitLength r.width
  omega

/-- `prop:time`, paper/paper.tex: the physical column budget
includes the exact record loop, parsing, setup and output. -/
noncomputable def columnBudget (r : ColumnRequest) : ℕ :=
  langBudget recordCallee recordSizes VV MM (columnInput r)
    (1000*(r.tests.length+1)*((ctxOf recordCallee recordSizes (columnInput r)).Wd+1))

/-- `sec:algorithm`, paper/paper.tex: an actual word function
reduces all strict tests of a column, retaining arbitrary signed moments. -/
noncomputable def columnMachine : WordFunction ColumnRequest columnInput columnOutput columnBudget :=
  wordFunction_of_lang columnInput columnOutput recordCallee recordSizes columnProgram
    (fun r => 1000*(r.tests.length+1)*((ctxOf recordCallee recordSizes (columnInput r)).Wd+1)) (by
      intro r
      obtain ⟨b,n,he,hn,hb⟩ := columnProgram_run
        (ctxOf recordCallee recordSizes (columnInput r)) r.width r.tests rfl
        (column_context_width r) r.countFits r.fieldsFit
      exact ⟨b,n,he,hb,hn⟩) (by
      intro r
      have h := column_context_width r
      change 1 ≤ (ctxOf recordCallee recordSizes (columnInput r)).Wd
      omega)

end NearQuarticWires.StageCert
