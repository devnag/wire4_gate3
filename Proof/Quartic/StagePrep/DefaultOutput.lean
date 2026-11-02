import Proof.Quartic.StagePrep.WordCases
import Proof.Gates.Dispatch.Macros

/-!
# The literal default output of preparation

Paper: `sec:params`, paper/paper.tex, and
preparation in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces

/-- The raw default word of `sec:params`, paper/paper.tex. -/
def defaultPreparationWord : List Bool := false :: outputWord Algorithm.soundDefault

/-- The actual default emitter of `sec:params`, paper/paper.tex. -/
def defaultPreparationOutput : St VV := emitL defaultPreparationWord

/-- The default output of `sec:params`, paper/paper.tex, is written in constant time with no input reads. -/
theorem defaultPreparationOutput_spec (C : Ctx) (a : DS VV) (hc : Cst a) :
    Hs C defaultPreparationOutput a (2 * defaultPreparationWord.length + 1) (fun b =>
      b.out = a.out ++ defaultPreparationWord ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Fr a b [vJ]) := by
  refine Hs.mono (emitL_spec defaultPreparationWord a) le_rfl ?_
  rintro b ⟨hb, hcp, hwq, hfr⟩
  exact ⟨hb, hcp, hwq, Cst.of_fr hc hfr (by decide)
    (by rw [hfr _ (by decide), hcp]; exact hc.pos), hfr⟩

/-- Every nonnormalized call has the exact physical default
`prepWord` of `sec:params`, paper/paper.tex. -/
theorem defaultPreparationOutput_not_admitted (C : Ctx) (B1 B2 : ℕ)
    (c : Call) (w : List Bool) (ha : ¬ Transfer.Admitted4 B1 B2 c)
    (a : DS VV) (hc : Cst a) :
    Hs C defaultPreparationOutput a (2 * defaultPreparationWord.length + 1) (fun b =>
      b.out = a.out ++ Program.prepWord B1 B2 c w ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Fr a b [vJ]) := by
  rw [prepWord_of_not_admitted c w ha]
  exact defaultPreparationOutput_spec C a hc

end NearQuarticWires.StagePrep
