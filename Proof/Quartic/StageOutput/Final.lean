import Proof.Quartic.StageOutput.WordFunction
import Proof.Quartic.Cells.ParametersOutputRuntime

/-!
# The ordinary polynomial-time output stage

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The single ordinary program reads the nine semantic inputs
of Step 5 and prints the exact center-radius pair. Its full physical cost,
including padding, framing, arithmetic and reduced-rational printing, is
polynomial in the original call-word length on every call and witness.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

/-- The exact polynomial-cost field paired with `StageOutput.output`. -/
theorem outputCost (B1 B2 : ℕ) : Program.PolyCost (outputBudget B1 B2) :=
  Cells.outputBudget_polynomial B1 B2

end NearQuarticWires.StageOutput
