import Proof.Quartic.StageColumns.Program
import Proof.Gates.Cells.Run
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the physical
common-generator printer invokes no external subroutine. -/
noncomputable def columnCallee : Callee :=
  ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    wordFunction_of_wmx (WMX.skip : WMX 1 0) 1 (by decide) (fun _ => 0) (fun e => e.elim)⟩

def columnSizes : Sz := ⟨64, 1, 0, 0, 0, 0⟩

theorem input_leadOnes (P : StarParams) : leadOnes (columnInput P) = natBitLength P.n := by
  unfold columnInput
  simp only [List.append_assoc]
  exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _

/-- `prop:time`, paper/paper.tex: the original
first dimension field supplies sufficient ordinary binary workspace. -/
theorem columnWidth (P : StarParams) : P.n + 4 ≤ columnSizes.W (leadOnes (columnInput P)) := by
  have hn := lt_natBitLength P.n
  have hp := Nat.one_le_two_pow (n := natBitLength P.n)
  simp only [columnSizes, Sz.W, one_mul, input_leadOnes]
  omega

/-- `prop:time`, paper/paper.tex: this is the
complete compiled clock, including cold setup and actual head reset. -/
noncomputable def columnBudget (P : StarParams) : ℕ :=
  langBudget columnCallee columnSizes VV MM (columnInput P) (sourceClock P)

/-- `imp:partition` and `lem:print`, paper/paper.tex: a genuine cold ordinary machine maps the four original
parameters to the exact already-framed common-generator columns field. -/
noncomputable def columnWordFunction :
    WordFunction StarParams columnInput (fun P => PrimT.C4Geo.colsField P) columnBudget :=
  wordFunction_of_lang columnInput (fun P => PrimT.C4Geo.colsField P) columnCallee columnSizes
    program sourceClock (by
      intro P
      obtain ⟨b, n, he, hn, hout⟩ := program_run
        (ctxOf columnCallee columnSizes (columnInput P)) P rfl (columnWidth P)
      exact ⟨b, n, he, hout, hn⟩) (by
      intro P
      have := columnWidth P
      omega)

end NearQuarticWires.StageColumns
