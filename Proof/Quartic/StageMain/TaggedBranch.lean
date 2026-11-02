import Proof.Quartic.StageMain.TaggedCopy
import Proof.Gates.CounterMachine.TabCallDock

/-!
# The physical branch of a tagged ordinary call

Step 4 of `sec:algorithm`, paper/paper.tex, and
`prop:time`: a selected subroutine receives a copied
framed payload on a disjoint bank. Its framed answer is copied to the
common output. Every copy and every subroutine transition is charged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine

variable {ns nr : ℕ} {Req : Type} {input output : Req → List Bool} {budget : Req → ℕ}

noncomputable def branchProgram (f : WordFunction Req input (fun r => frame (output r)) budget)
    (bank : Fin f.program.tapeCount → Fin (ns + 1)) (src dst ruler : Fin (ns + 1))
    (OP : Fin nr) : WMX ns nr :=
  .seq (.wm (copyPayload src (bank (tape0 f.program)) OP))
    (.seq (.machZ f.program.machine bank ruler)
      (.wm (copyPayload (bank f.program.outputTape) dst OP)))

def branchCost (inputLength outputLength budget : ℕ) : ℕ :=
  100 * (inputLength + outputLength + budget + 1)

theorem branchProgram_run
    (f : WordFunction Req input (fun r => frame (output r)) budget) (r : Req)
    (cap : ℕ) (bank : Fin f.program.tapeCount → Fin (ns + 1))
    (src dst ruler : Fin (ns + 1)) (OP : Fin nr)
    (hinj : Function.Injective bank) (hsrc : ∀ j, bank j ≠ src)
    (hdst : ∀ j, bank j ≠ dst) (hruler : ∀ j, bank j ≠ ruler)
    (hsd : src ≠ dst) (hrs : ruler ≠ src) (σ : WState ns nr) (pre rest : List Bool)
    (hin : σ.st src = pre ++ frame (input r) ++ rest) (hsh : σ.sh src = pre.length)
    (hblank : ∀ j, σ.st (bank j) = []) (hzero : ∀ j, σ.sh (bank j) = 0)
    (hout : σ.st dst = []) (houth : σ.sh dst = 0) (hOP : σ.val OP = 0)
    (hL : σ.st ruler = List.replicate (budget r) false) (hLh : σ.sh ruler = 0)
    (hcapin : 2 * (input r).length + 2 ≤ cap)
    (hcapout : 2 * (output r).length + 2 ≤ cap) :
    ∃ τ, WXExec cap (branchProgram f bank src dst ruler OP) σ τ
      (branchCost (input r).length (output r).length (budget r)) ∧
      τ.st dst = frame (output r) := by
  let i := bank (tape0 f.program)
  have hcopy := copyPayload_run cap src i (hsrc _).symm OP pre (input r) rest σ
    hin hsh (hblank _) (hzero _) hOP hcapin
  let σ1 := (σ.sets i (frame (input r))).seth src (pre.length + 2 * (input r).length)
  have h1in : σ1.st (bank (tape0 f.program)) = frame (input r) := by simp [σ1, i]
  have h1blank : ∀ j, j ≠ tape0 f.program → σ1.st (bank j) = [] := by
    intro j hj
    have hji : bank j ≠ i := fun h => hj (hinj h)
    simp [σ1, Function.update_of_ne hji, hblank]
  have h1heads : ∀ j, σ1.sh (bank j) = 0 := by
    intro j
    simp [σ1, Function.update_of_ne (hsrc j), hzero]
  have h1L : σ1.st ruler = List.replicate (budget r) false := by
    simp [σ1, i, Function.update_of_ne (hruler _).symm, hL]
  have h1Lh : σ1.sh ruler = 0 := by simp [σ1, Function.update_of_ne hrs, hLh]
  obtain ⟨σ2, hcall, h2out, h2heads, h2other, h2val⟩ :=
    wfDock_exact f r cap bank hinj ruler hruler σ1 h1in h1blank h1heads
      (budget r) h1L h1Lh le_rfl
  have h2dst : σ2.st dst = [] := by
    rw [(h2other dst hdst).1]
    simp [σ1, i, Function.update_of_ne (hdst _).symm, hout]
  have h2dsth : σ2.sh dst = 0 := by
    rw [(h2other dst hdst).2]
    simp [σ1, Function.update_of_ne hsd.symm, houth]
  have h2OP : σ2.val OP = 0 := by rw [h2val]; exact hOP
  have hanswer := copyPayload_run cap (bank f.program.outputTape) dst (hdst _) OP
    [] (output r) [] σ2 (by simpa using h2out) (h2heads _) h2dst h2dsth h2OP hcapout
  refine ⟨_, (WXExec.seq (.wm hcopy) (WXExec.seq hcall (.wm hanswer))).mono ?_, ?_⟩
  · unfold branchCost
    omega
  · simp

end NearQuarticWires.StageMain.Tagged
