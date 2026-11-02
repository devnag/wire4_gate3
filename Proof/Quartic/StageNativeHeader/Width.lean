import Proof.Quartic.StageNativeHeader.CallAvoid

/-!
# The dense width from the column field

Paper: `lem:print`, paper/paper.tex.

`widthP` moves back to the start of the column field `frame (colsContent P)` on `sY`, copies it to `sY2`
(`StagePrint.appendFrameReset`), and reads its first number, the dense width `C4Geo.width P`, into `rW`
(`width_exec`). The column field on `sY` stays, its head at `0`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Control NearQuarticWires.StagePrint

variable (cap : ℕ)

/-- The output counter of the copy of the column field. -/
def rOY2 : Fin hnr := 17
/-- The source counter of that copy. -/
def rSCY : Fin hnr := 18

/-- Read the dense width. -/
noncomputable def widthP : WM hns hnr :=
  .seq (WM.rewind sY rOY) (.seq (appendFrameReset sY sY2 rOY2 rSCY) (.seq (WM.rewind sY2 rOY2)
    (readNatM true sY2 pf pc rW pp pt)))

theorem frame_colsContent (P : StarParams) : frame (colsContent P) =
    marks (natWord (PrimT.C4Geo.width P)) ++
      (marks (MatrixScorePhi.columnsWord (PrimT.C4Geo.width P) (PrimT.C4Geo.cols P)) ++ [false]) := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks]; simp [colsContent, marks_append]

/-- The cost of `widthP`. -/
def widthCost (P : StarParams) : ℕ := 60 * (frame (colsContent P)).length + readCost (PrimT.C4Geo.width P) + 20

/-- **The dense width.** -/
theorem width_exec (P : StarParams) (σ : WState hns hnr) (hY : σ.st sY = frame (colsContent P))
    (hYh : σ.sh sY = (frame (colsContent P)).length) (vOY : σ.val rOY = (frame (colsContent P)).length)
    (hY2 : σ.st sY2 = []) (hY2h : σ.sh sY2 = 0)
    (hz : ∀ y ∈ [rOY2, rSCY, pf, pc, pp, pt, rW], σ.val y = 0)
    (hcap : 4 * (frame (colsContent P)).length + 4 ≤ cap)
    (hcapW : 2 ^ (natBitLength (PrimT.C4Geo.width P) + 1) ≤ cap) :
    ∃ τ, WExec cap widthP σ τ (widthCost P) ∧ SOnly σ τ [sY, sY2] [rOY, rW] ∧ τ.st sY = σ.st sY ∧
      τ.sh sY = 0 ∧ τ.val rOY = 0 ∧ τ.val rW = PrimT.C4Geo.width P := by
  set F := frame (colsContent P) with hF
  have hFl : F.length = 2 * (colsContent P).length + 1 := by rw [hF]; exact RepairOrdinary.frame_length _
  have e1 := wrewind_spec cap sY rOY F.length σ vOY (by omega)
  set σ1 := (σ.setv rOY 0).seth sY (σ.sh sY - F.length) with hσ1
  have hY2Y : sY2 ≠ sY := sne (by simp [sY, sY2, strm])
  have e2 := appendFrameReset_spec cap sY sY2 rOY2 rSCY (Ne.symm hY2Y) (by decide) (colsContent P) [] σ1
    (by simp [hσ1, hY, hF]) (by simp [hσ1, hYh])
    (by simp [hσ1, Function.update_of_ne hY2Y, hY2, hY2h])
    (by simp [hσ1, Function.update_of_ne (show (rSCY : Fin hnr) ≠ rOY by decide), hz rSCY (by simp)])
    (by simp [hσ1, Function.update_of_ne (show (rOY2 : Fin hnr) ≠ rOY by decide), hz rOY2 (by simp)]; omega)
  set σ2 := appendO σ1 sY2 rOY2 F with hσ2
  have v2 : σ2.val rOY2 = F.length := by
    simp [hσ2, hσ1, Function.update_of_ne (show (rOY2 : Fin hnr) ≠ rOY by decide), hz rOY2 (by simp)]
  have e3 := wrewind_spec cap sY2 rOY2 F.length σ2 v2 (by omega)
  set σ3 := (σ2.setv rOY2 0).seth sY2 (σ2.sh sY2 - F.length) with hσ3
  have s3 : σ3.st sY2 = [] ++ marks (natWord (PrimT.C4Geo.width P)) ++
      (marks (MatrixScorePhi.columnsWord (PrimT.C4Geo.width P) (PrimT.C4Geo.cols P)) ++ [false]) := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hY2Y, hY2, hF, frame_colsContent]
  have h3 : σ3.sh sY2 = ([] : List Bool).length := by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hY2Y, hY2h]
  have hv3 : ∀ y, y ∉ [rOY, rOY2] → σ3.val y = σ.val y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
  obtain ⟨τ, e4, f4, s4, h4, v4⟩ := readStep cap sY2 rW (by decide) (PrimT.C4Geo.width P) [] _ σ3 s3 h3
    (fun y hy => by
      rw [hv3 y (by revert hy; revert y; decide)]
      exact hz y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    hcapW
  refine ⟨τ, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by
    unfold widthCost appendFrameCost; simp [RepairOrdinary.frame_length] at *; omega), ⟨fun i hi => ?_,
    fun i hi => ?_, fun y hy => ?_⟩, ?_, ?_, ?_, v4⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [f4.st i (by simp; exact hi.2)]
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hi.1, Function.update_of_ne hi.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [f4.sh i (by simp; exact hi.2)]
    simp [hσ3, hσ2, hσ1, Function.update_of_ne hi.1, Function.update_of_ne hi.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f4.val y (by simp; exact hy.2)]
    by_cases h : y = rOY2
    · subst h; simp [hσ3, hz rOY2 (by simp)]
    · exact hv3 y (by simp; exact ⟨hy.1, h⟩)
  · rw [f4.st sY (by simp [Ne.symm hY2Y])]
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hY2Y)]
  · rw [f4.sh sY (by simp [Ne.symm hY2Y])]
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (Ne.symm hY2Y), hYh]
  · rw [f4.val rOY (by decide)]
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (show (rOY : Fin hnr) ≠ rOY2 by decide)]

end NearQuarticWires.StageNativeHeader
