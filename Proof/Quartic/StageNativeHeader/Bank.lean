import Proof.Quartic.StageNativeHeader.Parse

/-!
# The input of the column printer

Paper: `lem:print`, paper/paper.tex.

`bankP` writes `frame (columnInput P)` (the four fields `n, r, b, s`) on the input tape of the call site of the
column printer, from the registers, and moves its head back to `0` (`bank_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (writeNatM writeNatM_spec appendO appendO_st appendO_sh
  appendO_val appendO_cell appendO_append appendO_nil appendO_setv)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

variable (cap : ℕ)

/-- The input tape of the column printer. -/
noncomputable def sB0 : Fin (hns + 1) := sbank ⟨0, Nat.lt_of_lt_of_le (by norm_num) colWF.program.twoTapes⟩

theorem sB0_eq : sB0 = site.bank (NearCubicGates.Close.WorkerArith.inTape colWF.program) := rfl

/-- The output counter of the bank input. -/
def rOB : Fin hnr := 15

/-- The registers of the number writers. -/
def wRN : Fin 8 ↪ Fin hnr := ⟨![rN, 9, 10, 11, 12, 13, 14, 15], by decide⟩
def wRR : Fin 8 ↪ Fin hnr := ⟨![rR, 9, 10, 11, 12, 13, 14, 15], by decide⟩
def wRB : Fin 8 ↪ Fin hnr := ⟨![rB, 9, 10, 11, 12, 13, 14, 15], by decide⟩
def wRS : Fin 8 ↪ Fin hnr := ⟨![rS, 9, 10, 11, 12, 13, 14, 15], by decide⟩

/-- Write `frame (columnInput P)` on the input tape of the call site. -/
noncomputable def bankP : WM hns hnr :=
  .seq (writeNatM sB0 wRN) (.seq (writeNatM sB0 wRR)
    (.seq (writeNatM sB0 wRB) (.seq (writeNatM sB0 wRS)
      (.seq (emitC sB0 rOB false) (WM.rewind sB0 rOB)))))

/-- The cost of writing `v`. -/
def writeCost (v : ℕ) : ℕ := (natBitLength v + 10) * (100 * v + 200)

/-- The cost of `bankP`. -/
def bankCost (P : StarParams) : ℕ :=
  writeCost P.n + writeCost P.r + writeCost P.b + writeCost P.s + 12 * (StageColumns.columnInput P).length + 60

theorem frame_columnInput (P : StarParams) : frame (StageColumns.columnInput P) =
    marks (natWord P.n) ++ marks (natWord P.r) ++ marks (natWord P.b) ++ marks (natWord P.s) ++ [false] := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks]
  simp [StageColumns.columnInput, marks_append]

/-- One number written on the bank input. -/
theorem writeStep (R : Fin 8 ↪ Fin hnr) (hR : ∀ i : Fin 8, i ≠ 0 → R i = ![rN, 9, 10, 11, 12, 13, 14, 15] i)
    (σ : WState hns hnr)
    (hz : ∀ y ∈ ([9, 10, 11, 12, 13, 14] : List (Fin hnr)), σ.val y = 0) (ho : σ.sh sB0 = (σ.st sB0).length)
    (hcap : σ.val (R 0) + σ.val rOB + 6 * natBitLength (σ.val (R 0)) + 6 ≤ cap) :
    WExec cap (writeNatM sB0 R) σ (appendO σ sB0 rOB (marks (natWord (σ.val (R 0))))) (writeCost (σ.val (R 0))) := by
  have e := writeNatM_spec cap sB0 R σ (by rw [hR 1 (by decide)]; exact hz 9 (by simp))
    (by rw [hR 2 (by decide)]; exact hz 10 (by simp)) (by rw [hR 3 (by decide)]; exact hz 11 (by simp))
    (by rw [hR 4 (by decide)]; exact hz 12 (by simp)) (by rw [hR 5 (by decide)]; exact hz 13 (by simp))
    (by rw [hR 6 (by decide)]; exact hz 14 (by simp)) ho (by rw [hR 7 (by decide)]; exact hcap)
  rw [hR 7 (by decide)] at e
  exact e

/-- **The input of the column printer.** -/
theorem bank_exec (P : StarParams) (σ : WState hns hnr) (hB : σ.st sB0 = []) (hBh : σ.sh sB0 = 0)
    (vN : σ.val rN = P.n) (vR : σ.val rR = P.r) (vB : σ.val rB = P.b) (vS : σ.val rS = P.s)
    (hz : ∀ y ∈ ([9, 10, 11, 12, 13, 14, 15] : List (Fin hnr)), σ.val y = 0)
    (hcap : 8 * (StageColumns.columnInput P).length + P.n + P.r + P.b + P.s + 100 ≤ cap) :
    ∃ τ, WExec cap bankP σ τ (bankCost P) ∧ SOnly σ τ [sB0] [] ∧
      τ.st sB0 = frame (StageColumns.columnInput P) ∧ τ.sh sB0 = 0 := by
  have hl := congrArg List.length (frame_columnInput P)
  simp only [List.length_append, Streaming.marks_length, RepairOrdinary.frame_length, List.length_cons,
    List.length_nil] at hl
  have l1 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length P.n
  have l2 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length P.r
  have l3 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length P.b
  have l4 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length P.s
  have hnbl : ∀ x, natBitLength x ≤ (natWord x).length := fun x => by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; omega
  have z0 : ∀ y ∈ ([9, 10, 11, 12, 13, 14] : List (Fin hnr)), σ.val y = 0 := fun y hy =>
    hz y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
  have hO : σ.val rOB = 0 := hz rOB (by simp [rOB])
  -- n
  have e1 := writeStep cap wRN (by decide) σ z0 (by rw [hB, hBh]; rfl)
    (by rw [show wRN 0 = rN from rfl, vN, hO]; have := hnbl P.n; have := hnbl P.r; omega)
  rw [show wRN 0 = rN from rfl, vN] at e1
  set σ1 := appendO σ sB0 rOB (marks (natWord P.n)) with hσ1
  have v1 : ∀ y, y ≠ rOB → σ1.val y = σ.val y := fun y h => by simp [hσ1, Function.update_of_ne h]
  -- r
  have e2 := writeStep cap wRR (by decide) σ1 (fun y hy => by
      rw [v1 y (by revert hy; revert y; decide)]; exact z0 y hy) (by simp [hσ1, hB, hBh])
    (by rw [show wRR 0 = rR from rfl, v1 _ (by decide), vR]; simp [hσ1, hO]; have := hnbl P.n; have := hnbl P.r
        omega)
  rw [show wRR 0 = rR from rfl, v1 _ (by decide), vR, appendO_append] at e2
  set σ2 := appendO σ sB0 rOB (marks (natWord P.n) ++ marks (natWord P.r)) with hσ2
  have v2 : ∀ y, y ≠ rOB → σ2.val y = σ.val y := fun y h => by simp [hσ2, Function.update_of_ne h]
  -- b
  have e3 := writeStep cap wRB (by decide) σ2 (fun y hy => by
      rw [v2 y (by revert hy; revert y; decide)]; exact z0 y hy) (by simp [hσ2, hB, hBh])
    (by rw [show wRB 0 = rB from rfl, v2 _ (by decide), vB]; simp [hσ2, hO]; have := hnbl P.n
        have := hnbl P.r; have := hnbl P.b; omega)
  rw [show wRB 0 = rB from rfl, v2 _ (by decide), vB, appendO_append] at e3
  set σ3 := appendO σ sB0 rOB (marks (natWord P.n) ++ marks (natWord P.r) ++ marks (natWord P.b)) with hσ3
  have v3 : ∀ y, y ≠ rOB → σ3.val y = σ.val y := fun y h => by simp [hσ3, Function.update_of_ne h]
  -- s
  have e4 := writeStep cap wRS (by decide) σ3 (fun y hy => by
      rw [v3 y (by revert hy; revert y; decide)]; exact z0 y hy) (by simp [hσ3, hB, hBh])
    (by rw [show wRS 0 = rS from rfl, v3 _ (by decide), vS]; simp [hσ3, hO]; have := hnbl P.n
        have := hnbl P.r; have := hnbl P.b; have := hnbl P.s; omega)
  rw [show wRS 0 = rS from rfl, v3 _ (by decide), vS, appendO_append] at e4
  set σ4 := appendO σ sB0 rOB (marks (natWord P.n) ++ marks (natWord P.r) ++ marks (natWord P.b) ++
    marks (natWord P.s)) with hσ4
  -- the end mark
  have e5 := NearQuarticWires.Control.emitC_app cap sB0 rOB false σ4 (by simp [hσ4, hB, hBh]) (by simp [hσ4, hO]; omega)
  rw [hσ4, appendO_append, ← frame_columnInput] at e5
  set σ5 := appendO σ sB0 rOB (frame (StageColumns.columnInput P)) with hσ5
  -- back to the start
  have e6 := wrewind_spec cap sB0 rOB _ σ5 rfl (by simp [hσ5, hO]; omega)
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_, ?_, ?_, ?_⟩
  · simp [hσ5, hO]
    unfold bankCost
    omega
  · refine ⟨fun i hi => ?_, fun i hi => ?_, fun y _ => ?_⟩
    · have : i ≠ sB0 := by simpa using hi
      simp [hσ5, Function.update_of_ne this]
    · have : i ≠ sB0 := by simpa using hi
      simp [hσ5, Function.update_of_ne this]
    · by_cases hy : y = rOB
      · subst hy; simp [hO]
      · simp [hσ5, Function.update_of_ne hy]
  · simp [hσ5, hB]
  · simp [hσ5, hB, hBh]

end NearQuarticWires.StageNativeHeader
