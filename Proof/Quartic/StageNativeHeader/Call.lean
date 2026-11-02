import Proof.Quartic.StageNativeHeader.Bank

/-!
# The call of the column printer

Paper: `imp:partition` and `lem:print`, paper/paper.tex.

`callAppendProgram site sY rOY` runs the sealed column printer `StageColumns.columnWordFunction` on
`frame (columnInput P)`, appends its output `colsField P = frame (colsContent P)` to `sY` and erases the bank
(`call_exec`). The state after it reads like `calledIdeal` (`SimW`); the call never touches `sOUT` (`call_avoids`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (SimW)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Control NearQuarticWires.StagePrint

variable (cap : ℕ)

/-- The output counter of the column field. -/
def rOY : Fin hnr := 16

/-- The column printer, its output written as a frame. -/
noncomputable def colWF' : WordFunction StarParams StageColumns.columnInput (fun P => frame (colsContent P))
    StageColumns.columnBudget := colWF

/-- The ideal state after the call. -/
noncomputable def calledIdeal (σ : WState hns hnr) (tapes : Fin tc → List Bool) (steps : ℕ) (P : StarParams) :
    WState hns hnr :=
  cleanState site (appendO (calledState site σ tapes (StageColumns.columnInput P).length steps) sY rOY
    (frame (colsContent P)))

/-- A stream outside the call site. -/
def OffSite (i : Fin (hns + 1)) : Prop := 13 ≤ i.val → False

theorem offSite_bank (i : Fin (hns + 1)) (hi : i.val < 10) : ∀ j, sbank j ≠ i := fun j h => by
  have := congrArg Fin.val h; simp [sbank] at this; omega

/-- **The streams after the call.** -/
theorem calledIdeal_st (σ : WState hns hnr) (tapes : Fin tc → List Bool) (steps : ℕ) (P : StarParams)
    (i : Fin (hns + 1)) (hi : i.val < 10) (hY : i ≠ sY) :
    (calledIdeal σ tapes steps P).st i = σ.st i ∧ (calledIdeal σ tapes steps P).sh i = σ.sh i := by
  have hb : ∀ j, site.bank j ≠ i := offSite_bank i hi
  have hT : i ≠ site.tally := sne (by simp [site, sTA, strm]; omega)
  have hG : i ≠ site.guard := sne (by simp [site, sGA, strm]; omega)
  constructor
  · simp only [calledIdeal, cleanState, calledState, WState.sets_st, Function.update_of_ne hG,
      Function.update_of_ne hT]
    rw [NearCubicGates.Close.WordPrograms.updS_st_other site.bank _ _ _ i hb]
    simp only [appendO_st, Function.update_of_ne hY, WState.sets_st, Function.update_of_ne hG,
      Function.update_of_ne hT]
    exact NearCubicGates.Close.WordPrograms.updS_st_other site.bank _ _ _ i hb
  · simp only [calledIdeal, cleanState, calledState, WState.sets_sh]
    rw [NearCubicGates.Close.WordPrograms.updS_sh_other site.bank _ _ _ i hb]
    simp only [appendO_sh, Function.update_of_ne hY, WState.sets_sh]
    exact NearCubicGates.Close.WordPrograms.updS_sh_other site.bank _ _ _ i hb

theorem calledIdeal_Y (σ : WState hns hnr) (tapes : Fin tc → List Bool) (steps : ℕ) (P : StarParams) :
    (calledIdeal σ tapes steps P).st sY = σ.st sY ++ frame (colsContent P) ∧
      (calledIdeal σ tapes steps P).sh sY = σ.sh sY + (frame (colsContent P)).length := by
  have hb : ∀ j, site.bank j ≠ sY := offSite_bank sY (by simp [sY, strm])
  have hT : sY ≠ site.tally := sne (by simp [sY, site, sTA, strm])
  have hG : sY ≠ site.guard := sne (by simp [sY, site, sGA, strm])
  constructor
  · simp only [calledIdeal, cleanState, calledState, WState.sets_st, Function.update_of_ne hG,
      Function.update_of_ne hT]
    rw [NearCubicGates.Close.WordPrograms.updS_st_other site.bank _ _ _ sY hb]
    simp only [appendO_st, Function.update_self, WState.sets_st, Function.update_of_ne hG, Function.update_of_ne hT]
    rw [NearCubicGates.Close.WordPrograms.updS_st_other site.bank _ _ _ sY hb]
  · simp only [calledIdeal, cleanState, calledState, WState.sets_sh]
    rw [NearCubicGates.Close.WordPrograms.updS_sh_other site.bank _ _ _ sY hb]
    simp only [appendO_sh, Function.update_self, WState.sets_sh]
    rw [NearCubicGates.Close.WordPrograms.updS_sh_other site.bank _ _ _ sY hb]

theorem calledIdeal_val (σ : WState hns hnr) (tapes : Fin tc → List Bool) (steps : ℕ) (P : StarParams) :
    (calledIdeal σ tapes steps P).val = Function.update σ.val rOY (σ.val rOY + (frame (colsContent P)).length) := by
  simp [calledIdeal, cleanState, calledState, updS]

/-- **The call of the column printer.** -/
theorem call_exec (P : StarParams) (σ : WState hns hnr)
    (hbank : ∀ j : Fin tc, σ.st (sbank j) = if j.val = 0 then frame (StageColumns.columnInput P) else [])
    (h0 : ∀ j : Fin tc, σ.sh (sbank j) = 0) (hTA : σ.st sTA = []) (hTAh : σ.sh sTA = 0) (hGA : σ.st sGA = [])
    (hGAh : σ.sh sGA = 0) (hL : σ.st sL = []) (hLh : σ.sh sL = 0) (hR : ∀ i, σ.val (siteRegs i) = 0)
    (hY : σ.st sY = []) (hYh : σ.sh sY = 0)
    (hcap : 2 * (StageColumns.columnInput P).length + 2 + StageColumns.columnBudget P ≤ cap)
    (hcapOut : σ.val rOY + (frame (colsContent P)).length + 1 ≤ cap) :
    ∃ (tapes : Fin tc → List Bool) (steps : ℕ) (τ : WState hns hnr),
      WXExec cap (callAppendProgram site sY rOY) σ τ
        (callAppendCost (StageColumns.columnInput P).length (StageColumns.columnBudget P)) ∧
      SimW (calledIdeal σ tapes steps P) τ := by
  obtain ⟨tapes, steps, τ, -, e, sim⟩ := callAppend_exec colWF' P cap site sY rOY
    (offSite_bank sY (by simp [sY, strm])) (sne (by simp [sY, site, sTA, strm]))
    (sne (by simp [sY, site, sGA, strm])) (by simp [rOY, site, siteRegs, Fin.ext_iff, hnr]) σ
    (fun j => by
      show σ.st (sbank j) = _
      rw [hbank j]
      exact (NearCubicGates.Close.CheckedPCPP.program_inputTapes _ _ _).symm)
    h0 hTA hTAh hGA hGAh (by show NearCubicGates.Close.Worker.Blank (σ.st sL); rw [hL]; exact nil_blank) hLh hR
    (sne (by simp [sY, site, sL, strm])) (by rw [hY, hYh]; rfl) hcap hcapOut
  exact ⟨tapes, steps, τ, e, sim⟩

end NearQuarticWires.StageNativeHeader
