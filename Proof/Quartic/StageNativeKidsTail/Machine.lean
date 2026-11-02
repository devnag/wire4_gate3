import Proof.Quartic.StageNativeKidsTail.CallOutput

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsTail

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab
open StageNativeKids StageResize

noncomputable def actualBudget (r : ResizeTailRequest) : ℕ := 2*tailSteps r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual cold ordinary program pays acquisition,
one resize computation, raw output copying and complete head reset. -/
noncomputable def tailWordFunction (f : ResizeCallee) :
    WordFunction ResizeTailRequest ResizeTailRequest.word ResizeTailRequest.output actualBudget :=
  wordFunction_of_ideal (tailProgram f) (out f.program.tapeCount)
    (by simp [out]) capacity (fun r=>lens f.program.tapeCount r.stream.budget)
    tailSteps (fun _=>le_rfl) (fun r=>⟨by simp [lens,out],tailProgram_run f r⟩)

/-- `prop:time`, paper/paper.tex: actual source
and concrete resize prices pay every finite copier and framing cost,
without any runtime count or output-length oracle. -/
theorem actualBudget_le (r : ResizeTailRequest) : actualBudget r≤r.budget := by
  have ho:=output_length_le r
  have hsq:=Nat.le_mul_self (r.word.length+r.stream.budget+1)
  unfold actualBudget tailSteps ResizeTailRequest.budget
  nlinarith

/-- `prop:time`, paper/paper.tex: replacing a
proved ordinary clock by a larger bound preserves the literal program. -/
noncomputable def enlargeBudget {Request : Type} {input output : Request→List Bool}
    {old new : Request→ℕ} (f : WordFunction Request input output old) (hb : ∀ r,old r≤new r) :
    WordFunction Request input output new where
  program:=f.program
  realizes:=by
    intro r
    obtain ⟨receipt,hr,ho⟩:=f.realizes r
    have hm:=run_moreFuel f.program.machine (old r) (new r-old r)
      (f.program.inputTapes (input r)) receipt hr
    rw [Nat.add_sub_of_le (hb r)] at hm
    exact ⟨receipt,hm,ho⟩

/-- `lem:print`, paper/paper.tex: the complete
count-preserving tail invokes the concrete stream-resize computation
once, retains every original binary count bit and emits exactly the
framed original-count plus raw resized records, including empty rows. -/
noncomputable def resizeTailWordFunction :
    WordFunction ResizeTailRequest ResizeTailRequest.word ResizeTailRequest.output ResizeTailRequest.budget :=
  enlargeBudget (tailWordFunction streamResizeWordFunction) actualBudget_le

end NearQuarticWires.StageNativeKidsTail
