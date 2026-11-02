import Proof.Quartic.Program.Assembly
import Proof.Quartic.Transfer.Reconcile4

/-!
# `thm:main` from the counter's two halves

Paper: `thm:main`, paper/paper.tex; `thm:counter`; Appendix A (the transfer).

The transfer `Transfer.transfer4_official` derives the statement `Statement.FinalStatement4` from the eight
intermediate inputs (`NineInputs`) and `CounterExists4`; `counterExists4_of_components` derives `CounterExists4` from the mathematical
half `Builder.CounterMath4` of the counting algorithm and the five stages `MachineComponents` of its program.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

/-- **`thm:main` from the eight inputs (`NineInputs`), the mathematical half of the counter and the stages of its program.** -/
theorem finalStatement4_of_components (inputs : NearCubicGates.Close.NineInputs)
    (hmath : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → ∃ M : Builder.CounterMath4 B1 B2, M.value = Builder.value)
    (hmachine : ∀ B1 B2 : ℕ, 0 < B1 → 0 < B2 → Nonempty (MachineComponents B1 B2)) :
    NearQuarticWires.Statement.FinalStatement4 :=
  Transfer.transfer4_official inputs (counterExists4_of_components hmath hmachine)

end NearQuarticWires.Program
