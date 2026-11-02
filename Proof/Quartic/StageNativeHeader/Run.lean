import Proof.Quartic.StageNativeHeader.Avoid

/-!
# The run of the native header printer

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`mainP E`: read the fields and write the input of the column printer (`preP`), call the column printer
(`callAppendProgram`), read the width, compute the dimensions and count the cuts (`postP`), emit the marked table
request on the accumulator (`E`), and copy it, read only, to the output with its end mark (`finalP`). For every
emission `E` with the specification of `EmitReady` (`EmitSpec`), the run prints exactly `frame (table.word)`
(`main_run`). The output stream is untouched before the copy (`call_avoids`, `post_avoids`), so it is exact
although the call is described up to reading.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq (SimW RdEq)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Control NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

/-- The specification of an emission. -/
def EmitSpec (E : WM hns hnr) : Prop :=
  ∀ (r : NativeHeaderRequest) (cap : ℕ), emitCap r ≤ cap → ∀ σ : WState hns hnr, EmitReady r σ →
    ∃ τ, WExec cap E σ τ (emitCost r) ∧ τ.st sACC = marks r.table.word ∧ τ.sh sACC = 0 ∧
      τ.val rFO = 0 ∧ τ.val rFC = 0

/-- The read-only copy to the output and the end mark. -/
noncomputable def finalP : WMX hns hnr := .seq (copyLoop false sACC sOUT rFO rFC) (.wm (emitC sOUT rFO false))

/-- **The native header printer**, for the emission `E`. -/
noncomputable def mainP (E : WM hns hnr) : WMX hns hnr :=
  .seq (.wm preP) (.seq (callAppendProgram site sY rOY) (.seq (.wm (.seq postP E)) finalP))

/-- The cost of the run. -/
noncomputable def runCost (r : NativeHeaderRequest) : ℕ :=
  preCost r + 1 + (callAppendCost (StageColumns.columnInput r.parameters).length
    (StageColumns.columnBudget r.parameters) + 1 + ((postCost r + 1 + emitCost r) + 1 +
      (r.table.word.length * 52 + 1 + 1 + 7)))

/-- The capacity of the run. -/
noncomputable def runCap (r : NativeHeaderRequest) : ℕ :=
  preCap r + postCap r + emitCap r + 2 * (StageColumns.columnInput r.parameters).length +
    StageColumns.columnBudget r.parameters + (frame (colsContent r.parameters)).length + 4 * r.table.word.length + 10

theorem sACC_ne_OUT : sACC ≠ sOUT := sne (by simp [sACC, sOUT, strm])

/-- **The run of the native header printer.** -/
theorem main_run (E : WM hns hnr) (hE : EmitSpec E) (hEA : WM.Avoids sOUT E) (r : NativeHeaderRequest) :
    ∃ τ, WXExec (runCap r) (mainP E) (start r) τ (runCost r) ∧ τ.st sOUT = frame r.table.word := by
  set cap := runCap r with hcapdef
  -- the fields and the column input
  obtain ⟨σA, eA, hA⟩ := pre_exec cap r (by rw [hcapdef]; unfold runCap; omega)
  have offA : ∀ i, i ≠ sIN → i ≠ sB0 → σA.st i = [] ∧ σA.sh i = 0 := hA.other
  have b0 : ∀ j : Fin tc, j.val = 0 → sbank j = sB0 := fun j h => by
    simp only [sB0]; congr 1; exact Fin.ext h
  have bne : ∀ j : Fin tc, j.val ≠ 0 → sbank j ≠ sB0 := fun j h e => h (by
    have := congrArg Fin.val e; simp [sbank, sB0] at this; exact this)
  have bIN : ∀ j : Fin tc, sbank j ≠ sIN := fun j => sne (by simp [sbank, sIN, strm])
  -- the column call
  obtain ⟨tapes, steps, τB, eB, simB⟩ := call_exec cap r.parameters σA
    (fun j => by
      by_cases hj : j.val = 0
      · rw [if_pos hj, b0 j hj]; exact hA.bank
      · rw [if_neg hj]; exact (offA _ (bIN j) (bne j hj)).1)
    (fun j => by
      by_cases hj : j.val = 0
      · rw [b0 j hj]; exact hA.bankh
      · exact (offA _ (bIN j) (bne j hj)).2)
    (offA sTA (sne (by simp [sTA, sIN, strm])) (sne (by simp [sTA, sB0, sbank, strm]))).1
    (offA sTA (sne (by simp [sTA, sIN, strm])) (sne (by simp [sTA, sB0, sbank, strm]))).2
    (offA sGA (sne (by simp [sGA, sIN, strm])) (sne (by simp [sGA, sB0, sbank, strm]))).1
    (offA sGA (sne (by simp [sGA, sIN, strm])) (sne (by simp [sGA, sB0, sbank, strm]))).2
    (offA sL (sne (by simp [sL, sIN, strm])) (sne (by simp [sL, sB0, sbank, strm]))).1
    (offA sL (sne (by simp [sL, sIN, strm])) (sne (by simp [sL, sB0, sbank, strm]))).2
    (fun i => hA.zero _ (by fin_cases i <;> decide))
    (offA sY (sne (by simp [sY, sIN, strm])) (sne (by simp [sY, sB0, sbank, strm]))).1
    (offA sY (sne (by simp [sY, sIN, strm])) (sne (by simp [sY, sB0, sbank, strm]))).2
    (by rw [hcapdef]; unfold runCap; omega)
    (by rw [hA.zero rOY (by decide), hcapdef]; unfold runCap; omega)
  -- the work before the emission, and the emission, on the state the call reads like
  obtain ⟨κ1, ePost, hReady⟩ := post_exec cap r _ (postPre_called r σA hA tapes steps)
    (by rw [hcapdef]; unfold runCap; omega)
  obtain ⟨κ2, eE, accE, acchE, oE, cE⟩ := hE r cap (by rw [hcapdef]; unfold runCap; omega) κ1 hReady
  obtain ⟨τC, eC, simC⟩ := NearCubicGates.Close.CheckedPCPP.wxexec_sim
    (WXExec.wm (cap := cap) (WExec.seq ePost eE)) τB simB
  -- the output is untouched so far
  have oA := offA sOUT (sne (by simp [sOUT, sIN, strm])) (sne (by simp [sOUT, sB0, sbank, strm]))
  have oB := WXExec.avoids eB call_avoids
  have oC := WXExec.avoids eC (show WMX.Avoids sOUT (.wm (.seq postP E)) from ⟨post_avoids, hEA⟩)
  have outC : τC.st sOUT = [] ∧ τC.sh sOUT = 0 := ⟨by rw [oC.1, oB.1, oA.1], by rw [oC.2, oB.2, oA.2]⟩
  -- the read-only copy
  have hread : ∀ q, readTapeBit (τC.st sACC) (τC.sh sACC + q) = readTapeBit (marks r.table.word ++ []) q := by
    intro q
    rw [simC.sh, acchE, Nat.zero_add, List.append_nil, ← accE]
    exact (simC.st sACC q).symm
  have vC : τC.val = κ2.val := simC.val
  have eF1 := copyLoop_exec_read cap τC sACC sOUT rFO rFC false sACC_ne_OUT (by decide) r.table.word [] hread rfl
    (by rw [outC.1, outC.2]; rfl) (by rw [vC, oE]; rw [hcapdef]; unfold runCap; omega)
    (by rw [vC, cE]; rw [hcapdef]; unfold runCap; omega)
  rw [bitCells_false] at eF1
  have hFO : (copySt τC sACC sOUT rFO rFC r.table.word.length (marks r.table.word)).st sOUT =
      marks r.table.word := by
    simp [copySt, outC.1]
  have eF2 := emitC_app cap sOUT rFO false (copySt τC sACC sOUT rFO rFC r.table.word.length (marks r.table.word))
    (by rw [hFO]; simp [copySt, Function.update_of_ne (Ne.symm sACC_ne_OUT), outC.2])
    (by simp [copySt, Function.update_of_ne (show (rFO : Fin hnr) ≠ rFC by decide), vC, oE]
        rw [hcapdef]; unfold runCap; omega)
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm eA) (WXExec.seq eB (WXExec.seq eC
    (WXExec.seq eF1 (WXExec.wm eF2))))) ?_, ?_⟩
  · unfold runCost; omega
  · simp [hFO, NearCubicGates.Close.Codec.frame_eq_marks]

end NearQuarticWires.StageNativeHeader
