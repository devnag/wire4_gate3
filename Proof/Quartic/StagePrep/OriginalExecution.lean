import Proof.Quartic.StagePrep.RawExecution
import Proof.Quartic.StagePrep.OriginalWidth

/-!
# Preparation on original cold requests

Paper: the encoded call of `thm:counter`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces

/-- One fixed native word width executes the actual complete
preparation program of `prop:time`, paper/paper.tex, on every original request. Its charge depends only
on the call and not on the witness suffix. -/
theorem originalPreparationExecution (B1 B2 : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (c : Call) (w : List Bool),
      ∃ b n, Ex (ctxOf K (callWord c) w) (rawPreparationProgram B1 B2) a0 b n ∧
        b.out=Program.prepWord B1 B2 c w ∧
        n ≤ rawPreparationCost B1 B2 (wdOf K (callWord c).length) c ∧
        b.wq ≤ 5*(c.n+1)^5 := by
  obtain ⟨K,hK,hwidth⟩ := originalPreparationWidth B1 B2
  refine ⟨K,hK,?_⟩
  intro c w
  obtain ⟨b,n,hex,hn,hout,_,hwq⟩ := rawPreparationProgram_spec
    (ctxOf K (callWord c) w) B1 B2 c rfl
    (hwidth (callWord c).length).1
    (hwidth (callWord c).length).2.1
    (hwidth (callWord c).length).2.2.1
    (hwidth (callWord c).length).2.2.2
  exact ⟨b,n,hex,hout,hn,hwq⟩

end NearQuarticWires.StagePrep
