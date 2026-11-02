import Proof.Quartic.StageMain.TaggedIdeal

/-!
# One ordinary word function for two tagged subroutines

Step 4 of `sec:algorithm`, paper/paper.tex, and
`prop:time`: the main controller uses a fixed selector
and disjoint tape banks. The physical cost is linear in the selected
input, selected answer and selected subroutine clock.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

variable {A B : Type} {ia oa : A → List Bool} {ib ob : B → List Bool}
  {ba : A → ℕ} {bb : B → ℕ}

theorem taggedProgram_run
    (f : WordFunction A ia (fun a => frame (oa a)) ba)
    (g : WordFunction B ib (fun b => frame (ob b)) bb) (request : A ⊕ B) :
    let l := f.program.tapeCount
    let r := g.program.tapeCount
    let cap := taggedCapacity ia oa ib ob ba bb request
    let σ := idealStart (l + r + 2) 1 (taggedInput ia ib request)
      (taggedLens l r (taggedBranchBudget ba bb request))
    ∃ τ, WXExec cap (taggedProgram f g) σ τ
      ((taggedCost ia oa ib ob ba bb request - 2) / 2) ∧
      τ.st 1 = frame (taggedAnswer oa ob request) := by
  let l := f.program.tapeCount
  let r := g.program.tapeCount
  cases request with
  | inl a =>
    let cap := taggedCapacity ia oa ib ob ba bb (.inl a)
    let σ := idealStart (l + r + 2) 1 (false :: ia a) (taggedLens l r (ba a))
    obtain ⟨τ, hbranch, hout⟩ := branchIdeal_run f a l r cap false (leftBank l r)
      (leftBank_injective l r) (leftBank_off l r)
      (by dsimp [cap, taggedCapacity, taggedInput, taggedAnswer, taggedBranchBudget]; omega)
      (by dsimp [cap, taggedCapacity, taggedInput, taggedAnswer, taggedBranchBudget]; omega)
    have e1 : WExec cap (.fwd (0 : Fin (l + r + 3))) σ (σ.seth 0 1) 1 := by
      simpa [σ, idealStart] using WExec.fwd (cap := cap) (0 : Fin (l + r + 3)) σ
    have hb : wbit (σ.seth 0 1) 0 = false := by
      simp [wbit, readTapeBit, σ, idealStart, frame]
    refine ⟨τ, (WXExec.seq (.wm e1) (WXExec.ifsF hb hbranch)).mono ?_, hout⟩
    dsimp [taggedCost, branchCost]
    omega
  | inr b =>
    let cap := taggedCapacity ia oa ib ob ba bb (.inr b)
    let σ := idealStart (l + r + 2) 1 (true :: ib b) (taggedLens l r (bb b))
    obtain ⟨τ, hbranch, hout⟩ := branchIdeal_run g b l r cap true (rightBank l r)
      (rightBank_injective l r) (rightBank_off l r)
      (by dsimp [cap, taggedCapacity, taggedInput, taggedAnswer, taggedBranchBudget]; omega)
      (by dsimp [cap, taggedCapacity, taggedInput, taggedAnswer, taggedBranchBudget]; omega)
    have e1 : WExec cap (.fwd (0 : Fin (l + r + 3))) σ (σ.seth 0 1) 1 := by
      simpa [σ, idealStart] using WExec.fwd (cap := cap) (0 : Fin (l + r + 3)) σ
    have hb : wbit (σ.seth 0 1) 0 = true := by
      simp [wbit, readTapeBit, σ, idealStart, frame]
    refine ⟨τ, (WXExec.seq (.wm e1) (WXExec.ifsT hb hbranch)).mono ?_, hout⟩
    dsimp [taggedCost, branchCost]
    omega

noncomputable def taggedWordFunction
    (f : WordFunction A ia (fun a => frame (oa a)) ba)
    (g : WordFunction B ib (fun b => frame (ob b)) bb) :
    WordFunction (A ⊕ B) (taggedInput ia ib) (fun r => frame (taggedAnswer oa ob r))
      (taggedCost ia oa ib ob ba bb) :=
  wordFunction_of_ideal (taggedProgram f g) 1 (by simp)
    (taggedCapacity ia oa ib ob ba bb)
    (fun r => taggedLens f.program.tapeCount g.program.tapeCount (taggedBranchBudget ba bb r))
    (fun r => (taggedCost ia oa ib ob ba bb r - 2) / 2)
    (by intro r; cases r <;> simp only [taggedCost] <;> omega)
    (by
      intro r
      refine ⟨?_, taggedProgram_run f g r⟩
      simp [taggedLens, (sharedRuler_off f.program.tapeCount g.program.tapeCount).2.symm])

end NearQuarticWires.StageMain.Tagged
