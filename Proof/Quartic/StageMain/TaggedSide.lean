import Proof.Quartic.StageMain.TaggedBranch

/-!
# Entering the selected main-pass subroutine

Step 4 of `sec:algorithm`, paper/paper.tex: after the
selector bit, the original input contains precisely the framed payload
for the chosen computation. Advancing over the tag is a charged step.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ} {Req : Type} {input output : Req → List Bool} {budget : Req → ℕ}

noncomputable def branchFromTag
    (f : WordFunction Req input (fun r => frame (output r)) budget)
    (bank : Fin f.program.tapeCount → Fin (ns + 1)) (src dst ruler : Fin (ns + 1))
    (OP : Fin nr) : WMX ns nr :=
  .seq (.wm (.fwd src)) (branchProgram f bank src dst ruler OP)

theorem branchFromTag_run
    (f : WordFunction Req input (fun r => frame (output r)) budget) (r : Req)
    (cap : ℕ) (bank : Fin f.program.tapeCount → Fin (ns + 1))
    (src dst ruler : Fin (ns + 1)) (OP : Fin nr)
    (hinj : Function.Injective bank) (hsrc : ∀ j, bank j ≠ src)
    (hdst : ∀ j, bank j ≠ dst) (hruler : ∀ j, bank j ≠ ruler)
    (hsd : src ≠ dst) (hrs : ruler ≠ src) (σ : WState ns nr) (tag : Bool)
    (hin : σ.st src = frame (tag :: input r)) (hsh : σ.sh src = 1)
    (hblank : ∀ j, σ.st (bank j) = []) (hzero : ∀ j, σ.sh (bank j) = 0)
    (hout : σ.st dst = []) (houth : σ.sh dst = 0) (hOP : σ.val OP = 0)
    (hL : σ.st ruler = List.replicate (budget r) false) (hLh : σ.sh ruler = 0)
    (hcapin : 2 * (input r).length + 2 ≤ cap)
    (hcapout : 2 * (output r).length + 2 ≤ cap) :
    ∃ τ, WXExec cap (branchFromTag f bank src dst ruler OP) σ τ
      (branchCost (input r).length (output r).length (budget r) + 2) ∧
      τ.st dst = frame (output r) := by
  have e1 : WExec cap (.fwd src) σ (σ.seth src (σ.sh src + 1)) 1 := WExec.fwd src σ
  obtain ⟨τ, e2, ho⟩ := branchProgram_run f r cap bank src dst ruler OP hinj hsrc hdst hruler
    hsd hrs (σ.seth src (σ.sh src + 1)) [true, tag] []
    (by simpa [frame] using hin) (by simp [hsh])
    hblank (by intro j; simp [Function.update_of_ne (hsrc j), hzero])
    hout (by simp [Function.update_of_ne hsd.symm, houth]) hOP hL
    (by simp [Function.update_of_ne hrs, hLh]) hcapin hcapout
  exact ⟨τ, (WXExec.seq (.wm e1) e2).mono (by omega), ho⟩

end NearQuarticWires.StageMain.Tagged
