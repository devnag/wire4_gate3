import Proof.Quartic.StageMain.TaggedProgram

/-!
# Cold initial states for the selected subroutine

Step 4 of `sec:algorithm`, paper/paper.tex: the original
word contains the selector and payload, every subroutine bank is blank,
and the exact branch clock supplies only its own reset bound.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

variable {Req : Type} {input output : Req → List Bool} {budget : Req → ℕ}

theorem branchIdeal_run (f : WordFunction Req input (fun r => frame (output r)) budget)
    (request : Req) (l r cap : ℕ) (tag : Bool)
    (bank : Fin f.program.tapeCount → Fin (l + r + 3))
    (hinj : Function.Injective bank)
    (hoff : ∀ j, bank j ≠ 0 ∧ bank j ≠ 1 ∧ bank j ≠ sharedRuler l r)
    (hcapin : 2 * (input request).length + 2 ≤ cap)
    (hcapout : 2 * (output request).length + 2 ≤ cap) :
    let σ := idealStart (l + r + 2) 1 (tag :: input request) (taggedLens l r (budget request))
    ∃ τ, WXExec cap (branchFromTag f bank 0 1 (sharedRuler l r) 0) (σ.seth 0 1) τ
      (branchCost (input request).length (output request).length (budget request) + 2) ∧
      τ.st 1 = frame (output request) := by
  let σ := idealStart (l + r + 2) 1 (tag :: input request) (taggedLens l r (budget request))
  have h10 : (1 : Fin (l + r + 3)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    change 1 % (l + r + 3) = 0 at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hr0 := (sharedRuler_off l r).1
  have hr1 := (sharedRuler_off l r).2
  apply branchFromTag_run f request cap bank 0 1 (sharedRuler l r) 0 hinj
    (fun j => (hoff j).1) (fun j => (hoff j).2.1) (fun j => (hoff j).2.2)
    h10.symm hr0 (σ.seth 0 1) tag
  · rfl
  · simp
  · intro j
    simp [σ, idealStart, (hoff j).1, taggedLens, (hoff j).2.2]
  · intro j
    simp [σ, idealStart, Function.update_of_ne (hoff j).1]
  · simp [σ, idealStart, taggedLens, hr1.symm]
  · simp [σ, idealStart]
  · rfl
  · simp [σ, idealStart, hr0, taggedLens]
  · simp [σ, idealStart, Function.update_of_ne hr0]
  · exact hcapin
  · exact hcapout

end NearQuarticWires.StageMain.Tagged
