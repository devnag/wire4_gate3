import Proof.Quartic.Reconstruct.Assembly
import Proof.Quartic.Reconstruct.PrintFinal

/-!
# The reconstruction control

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, and `prop:time`.

The five stages of the reconstruction, with the printing stage `printsStage`, give the reconstruction control of
every child evaluation (`reconstructControl`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearQuarticWires.Greedy

/-- **The reconstruction control** (Step 3 of `sec:algorithm`): the stages `prints ▹ tables ▹ systems ▹ solved ▹
total`. -/
noncomputable def reconstructControl : ∀ B1 B2 : ℕ, ReconstructControl B1 B2 :=
  fun B1 B2 => reconstructControl_of_prints (printsStage B1 B2)

end NearQuarticWires.Reconstruct
