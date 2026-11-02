import Proof.Quartic.Control.Loop

/-!
# The output word of Step 3

Paper: Step 3 of `sec:algorithm`, paper/paper.tex: after the `S` rounds, the word after Step 2 is
followed by the consistency bit and the chosen seed (`Greedy.seedSuffix`: `bitWord true ++ frame π` on a dispatched
call, nothing on any other call).

The output is written on an empty output stream by appending cells, from streams that need only *read* like the
word after Step 2 and the marked seed, so that the output is exact whatever trailing blanks the other streams carry.

* `writeSeed`: `frame (w ++ bitWord true ++ frame π)` (`writeSeed_exec`);
* `writeCopy`: `frame w` (`writeCopy_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO emitPair emitPair_spec appendO_st appendO_sh
  appendO_val appendO_cell)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

variable {ns nr : ℕ}

/-- **The output of a dispatched call**: `frame (w ++ bitWord true ++ frame π)` on `O`. -/
def writeSeed (IN P O : Fin (ns + 1)) (OP C : Fin nr) : WMX ns nr :=
  .seq (copyLoop false IN O OP C)
  (.seq (.wm (emitPair O OP true)) (.seq (.wm (emitPair O OP false)) (.seq (.wm (emitPair O OP true))
  (.seq (copyLoop true P O OP C)
  (.seq (.wm (emitPair O OP false)) (.wm (emitC O OP false)))))))

/-- **The output of any other call**: `frame w` on `O`. -/
def writeCopy (IN O : Fin (ns + 1)) (OP C : Fin nr) : WMX ns nr :=
  .seq (copyLoop false IN O OP C) (.wm (emitC O OP false))

theorem seedFrame_eq (w π : List Bool) :
    frame (w ++ NearCubicGates.Close.Interfaces.bitWord true ++ frame π) =
      marks w ++ [true, true, true, false, true, true] ++ marks (marks π) ++ [true, false] ++ [false] := by
  have hb : NearCubicGates.Close.Interfaces.bitWord true = [true, false, true] := by
    simp [NearCubicGates.Close.Interfaces.bitWord]; decide
  rw [hb, NearCubicGates.Close.Codec.frame_eq_marks, NearCubicGates.Close.Codec.frame_eq_marks]
  simp [marks, List.append_assoc]

/-- The cost bound of the output writers. -/
def writeOutCost (w p : ℕ) : ℕ := 60 * (w + p + 2)

section Write

variable (cap : ℕ) (σ : WState ns nr) (IN P O : Fin (ns + 1)) (OP C : Fin nr)

/-- **The output of a dispatched call.** If `IN` reads, from its head, like `frame w` and `P` like `marks π`, and `O`
is empty with its head at `0`, `writeSeed` leaves exactly `frame (w ++ bitWord true ++ frame π)` on `O`. -/
theorem writeSeed_exec (hIP : IN ≠ P) (hIO : IN ≠ O) (hPO : P ≠ O) (hOC : OP ≠ C) (w π : List Bool)
    (hIN : ∀ q, readTapeBit (σ.st IN) (σ.sh IN + q) = readTapeBit (marks w ++ [false]) q)
    (hP : ∀ q, readTapeBit (σ.st P) (σ.sh P + q) = readTapeBit (marks π ++ []) q)
    (hO : σ.st O = []) (hOh : σ.sh O = 0) (hOP : σ.val OP = 0) (hC : σ.val C = 0)
    (hc : 6 * w.length + 6 * π.length + 20 ≤ cap) :
    ∃ τ, WXExec cap (writeSeed IN P O OP C) σ τ (writeOutCost w.length π.length) ∧
      τ.st O = frame (w ++ NearCubicGates.Close.Interfaces.bitWord true ++ frame π) := by
  have e1 := copyLoop_exec_read cap σ IN O OP C false hIO hOC w [false] hIN rfl (by rw [hO, hOh]; rfl)
    (by omega) (by omega)
  rw [bitCells_false] at e1
  set σ1 := copySt σ IN O OP C w.length (marks w) with hσ1
  have h1O : σ1.st O = marks w := by simp [hσ1, copySt, hO]
  have h1Oh : σ1.sh O = (σ1.st O).length := by
    rw [h1O]; simp [hσ1, copySt, Function.update_of_ne hIO.symm, hOh, marks_length]
  have h1OP : σ1.val OP = 2 * w.length := by
    simp [hσ1, copySt, Function.update_of_ne hOC, hOP, marks_length]
  have e2 := emitPair_spec cap O OP true σ1 h1Oh (by omega)
  set σ2 := appendO σ1 O OP [true, true] with hσ2
  have e3 := emitPair_spec cap O OP false σ2 (by simp [hσ2, h1Oh]) (by simp [hσ2, h1OP]; omega)
  set σ3 := appendO σ2 O OP [true, false] with hσ3
  have e4 := emitPair_spec cap O OP true σ3 (by simp [hσ3, hσ2, h1Oh]) (by simp [hσ3, hσ2, h1OP]; omega)
  set σ4 := appendO σ3 O OP [true, true] with hσ4
  have h4P : ∀ q, readTapeBit (σ4.st P) (σ4.sh P + q) = readTapeBit (marks π ++ []) q := by
    intro q
    have h1 : σ4.st P = σ.st P := by
      simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hPO]
    have h2 : σ4.sh P = σ.sh P := by
      simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hPO, Function.update_of_ne hIP.symm]
    rw [h1, h2]; exact hP q
  have h4Ol : (σ4.st O).length = 2 * w.length + 6 := by simp [hσ4, hσ3, hσ2, h1O, marks_length]
  have h4Oh : σ4.sh O = (σ4.st O).length := by simp [hσ4, hσ3, hσ2, h1Oh]
  have h4OP : σ4.val OP = 2 * w.length + 6 := by simp [hσ4, hσ3, hσ2, h1OP]
  have h4C : σ4.val C = 2 * w.length := by
    simp [hσ4, hσ3, hσ2, hσ1, copySt, Function.update_of_ne hOC.symm, hC]
  have e5 := copyLoop_exec_read cap σ4 P O OP C true hPO hOC π [] h4P rfl h4Oh (by omega) (by omega)
  rw [bitCells_true] at e5
  set σ5 := copySt σ4 P O OP C π.length (marks (marks π)) with hσ5
  have h5Oh : σ5.sh O = (σ5.st O).length := by
    simp [hσ5, copySt, Function.update_of_ne hPO.symm, h4Oh]
  have h5OP : σ5.val OP = 2 * w.length + 6 + 4 * π.length := by
    simp [hσ5, copySt, Function.update_of_ne hOC, h4OP, marks_length]; ring
  have e6 := emitPair_spec cap O OP false σ5 h5Oh (by omega)
  set σ6 := appendO σ5 O OP [true, false] with hσ6
  have e7 := emitC_spec cap O OP false σ6 (by simp [hσ6, h5Oh]) (by simp [hσ6, h5OP]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.seq e5 (WXExec.seq (WXExec.wm e6) (WXExec.wm e7))))))) ?_, ?_⟩
  · unfold writeOutCost; omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [seedFrame_eq]
    simp [hσ6, hσ5, hσ4, hσ3, hσ2, copySt, h1O, List.append_assoc]

/-- **The output of any other call.** If `IN` reads, from its head, like `frame w`, and `O` is empty with its head at
`0`, `writeCopy` leaves exactly `frame w` on `O`. -/
theorem writeCopy_exec (hIO : IN ≠ O) (hOC : OP ≠ C) (w : List Bool)
    (hIN : ∀ q, readTapeBit (σ.st IN) (σ.sh IN + q) = readTapeBit (marks w ++ [false]) q)
    (hO : σ.st O = []) (hOh : σ.sh O = 0) (hOP : σ.val OP = 0) (hC : σ.val C = 0)
    (hc : 6 * w.length + 6 ≤ cap) :
    ∃ τ, WXExec cap (writeCopy IN O OP C) σ τ (writeOutCost w.length 0) ∧ τ.st O = frame w := by
  have e1 := copyLoop_exec_read cap σ IN O OP C false hIO hOC w [false] hIN rfl (by rw [hO, hOh]; rfl)
    (by omega) (by omega)
  rw [bitCells_false] at e1
  set σ1 := copySt σ IN O OP C w.length (marks w) with hσ1
  have h1O : σ1.st O = marks w := by simp [hσ1, copySt, hO]
  have h1Oh : σ1.sh O = (σ1.st O).length := by
    rw [h1O]; simp [hσ1, copySt, Function.update_of_ne hIO.symm, hOh, marks_length]
  have h1OP : σ1.val OP = 2 * w.length := by
    simp [hσ1, copySt, Function.update_of_ne hOC, hOP, marks_length]
  have e2 := emitC_spec cap O OP false σ1 h1Oh (by omega)
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.wm e2)) ?_, ?_⟩
  · unfold writeOutCost; omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, h1O]
    rw [NearCubicGates.Close.Codec.frame_eq_marks]

end Write


/-! ## The word after the coefficient stage -/

/-- **The output of the coefficient stage**: `frame (w ++ frame U)` on `O`, from `frame w` on `IN` and `marks U`
on `T`. -/
def writeTable (IN T O : Fin (ns + 1)) (OP C : Fin nr) : WMX ns nr :=
  .seq (copyLoop false IN O OP C)
  (.seq (copyLoop true T O OP C)
  (.seq (.wm (emitPair O OP false)) (.wm (emitC O OP false))))

theorem tableFrame_eq (w U : List Bool) : frame (w ++ frame U) = marks w ++ marks (marks U) ++ [true, false] ++ [false] := by
  rw [NearCubicGates.Close.Codec.frame_eq_marks, NearCubicGates.Close.Codec.frame_eq_marks]
  simp [marks, List.append_assoc]

section WriteTable

variable (cap : ℕ) (σ : WState ns nr) (IN T O : Fin (ns + 1)) (OP C : Fin nr)

/-- **The coefficient-stage output.** If `IN` reads, from its head, like `frame w` and `T` like `marks U`, and `O`
is empty with its head at `0`, `writeTable` leaves exactly `frame (w ++ frame U)` on `O`. -/
theorem writeTable_exec (hIT : IN ≠ T) (hIO : IN ≠ O) (hTO : T ≠ O) (hOC : OP ≠ C) (w U : List Bool)
    (hIN : ∀ q, readTapeBit (σ.st IN) (σ.sh IN + q) = readTapeBit (marks w ++ [false]) q)
    (hT : ∀ q, readTapeBit (σ.st T) (σ.sh T + q) = readTapeBit (marks U ++ []) q)
    (hO : σ.st O = []) (hOh : σ.sh O = 0) (hOP : σ.val OP = 0) (hC : σ.val C = 0)
    (hc : 6 * w.length + 6 * U.length + 20 ≤ cap) :
    ∃ τ, WXExec cap (writeTable IN T O OP C) σ τ (writeOutCost w.length U.length) ∧
      τ.st O = frame (w ++ frame U) := by
  have e1 := copyLoop_exec_read cap σ IN O OP C false hIO hOC w [false] hIN rfl (by rw [hO, hOh]; rfl)
    (by omega) (by omega)
  rw [bitCells_false] at e1
  set σ1 := copySt σ IN O OP C w.length (marks w) with hσ1
  have h1O : σ1.st O = marks w := by simp [hσ1, copySt, hO]
  have h1Oh : σ1.sh O = (σ1.st O).length := by
    rw [h1O]; simp [hσ1, copySt, Function.update_of_ne hIO.symm, hOh, marks_length]
  have h1OP : σ1.val OP = 2 * w.length := by
    simp [hσ1, copySt, Function.update_of_ne hOC, hOP, marks_length]
  have h1C : σ1.val C = 2 * w.length := by simp [hσ1, copySt, hC]
  have h1T : ∀ q, readTapeBit (σ1.st T) (σ1.sh T + q) = readTapeBit (marks U ++ []) q := by
    intro q
    have h1 : σ1.st T = σ.st T := by simp [hσ1, copySt, Function.update_of_ne hTO]
    have h2 : σ1.sh T = σ.sh T := by
      simp [hσ1, copySt, Function.update_of_ne hTO, Function.update_of_ne hIT.symm]
    rw [h1, h2]; exact hT q
  have e2 := copyLoop_exec_read cap σ1 T O OP C true hTO hOC U [] h1T rfl h1Oh (by omega) (by omega)
  rw [bitCells_true] at e2
  set σ2 := copySt σ1 T O OP C U.length (marks (marks U)) with hσ2
  have h2Oh : σ2.sh O = (σ2.st O).length := by
    simp [hσ2, copySt, Function.update_of_ne hTO.symm, h1Oh]
  have h2OP : σ2.val OP = 2 * w.length + 4 * U.length := by
    simp [hσ2, copySt, Function.update_of_ne hOC, h1OP, marks_length]; ring
  have e3 := emitPair_spec cap O OP false σ2 h2Oh (by omega)
  set σ3 := appendO σ2 O OP [true, false] with hσ3
  have e4 := emitC_spec cap O OP false σ3 (by simp [hσ3, h2Oh]) (by simp [hσ3, h2OP]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) (WXExec.wm e4)))) ?_, ?_⟩
  · unfold writeOutCost; omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [tableFrame_eq]
    simp [hσ3, hσ2, copySt, h1O, List.append_assoc]

end WriteTable

end NearQuarticWires.Control
